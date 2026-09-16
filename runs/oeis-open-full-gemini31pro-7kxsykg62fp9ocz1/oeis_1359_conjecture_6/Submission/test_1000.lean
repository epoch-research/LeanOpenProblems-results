import Mathlib
open Nat
lemma test_1000 : count Nat.Prime 1000 = 168 := by
  have c0 : count Nat.Prime 0 = 0 := count_zero (p := Nat.Prime)
  have p0 : ¬ Nat.Prime 0 := by norm_num
  have c1 : count Nat.Prime 1 = 0 := by rw [count_succ, c0, if_neg p0]
  have p1 : ¬ Nat.Prime 1 := by norm_num
  have c2 : count Nat.Prime 2 = 0 := by rw [count_succ, c1, if_neg p1]
  have p2 : Nat.Prime 2 := by norm_num
  have c3 : count Nat.Prime 3 = 1 := by rw [count_succ, c2, if_pos p2]
  have p3 : Nat.Prime 3 := by norm_num
  have c4 : count Nat.Prime 4 = 2 := by rw [count_succ, c3, if_pos p3]
  have p4 : ¬ Nat.Prime 4 := by norm_num
  have c5 : count Nat.Prime 5 = 2 := by rw [count_succ, c4, if_neg p4]
  have p5 : Nat.Prime 5 := by norm_num
  have c6 : count Nat.Prime 6 = 3 := by rw [count_succ, c5, if_pos p5]
  have p6 : ¬ Nat.Prime 6 := by norm_num
  have c7 : count Nat.Prime 7 = 3 := by rw [count_succ, c6, if_neg p6]
  have p7 : Nat.Prime 7 := by norm_num
  have c8 : count Nat.Prime 8 = 4 := by rw [count_succ, c7, if_pos p7]
  have p8 : ¬ Nat.Prime 8 := by norm_num
  have c9 : count Nat.Prime 9 = 4 := by rw [count_succ, c8, if_neg p8]
  have p9 : ¬ Nat.Prime 9 := by norm_num
  have c10 : count Nat.Prime 10 = 4 := by rw [count_succ, c9, if_neg p9]
  have p10 : ¬ Nat.Prime 10 := by norm_num
  have c11 : count Nat.Prime 11 = 4 := by rw [count_succ, c10, if_neg p10]
  have p11 : Nat.Prime 11 := by norm_num
  have c12 : count Nat.Prime 12 = 5 := by rw [count_succ, c11, if_pos p11]
  have p12 : ¬ Nat.Prime 12 := by norm_num
  have c13 : count Nat.Prime 13 = 5 := by rw [count_succ, c12, if_neg p12]
  have p13 : Nat.Prime 13 := by norm_num
  have c14 : count Nat.Prime 14 = 6 := by rw [count_succ, c13, if_pos p13]
  have p14 : ¬ Nat.Prime 14 := by norm_num
  have c15 : count Nat.Prime 15 = 6 := by rw [count_succ, c14, if_neg p14]
  have p15 : ¬ Nat.Prime 15 := by norm_num
  have c16 : count Nat.Prime 16 = 6 := by rw [count_succ, c15, if_neg p15]
  have p16 : ¬ Nat.Prime 16 := by norm_num
  have c17 : count Nat.Prime 17 = 6 := by rw [count_succ, c16, if_neg p16]
  have p17 : Nat.Prime 17 := by norm_num
  have c18 : count Nat.Prime 18 = 7 := by rw [count_succ, c17, if_pos p17]
  have p18 : ¬ Nat.Prime 18 := by norm_num
  have c19 : count Nat.Prime 19 = 7 := by rw [count_succ, c18, if_neg p18]
  have p19 : Nat.Prime 19 := by norm_num
  have c20 : count Nat.Prime 20 = 8 := by rw [count_succ, c19, if_pos p19]
  have p20 : ¬ Nat.Prime 20 := by norm_num
  have c21 : count Nat.Prime 21 = 8 := by rw [count_succ, c20, if_neg p20]
  have p21 : ¬ Nat.Prime 21 := by norm_num
  have c22 : count Nat.Prime 22 = 8 := by rw [count_succ, c21, if_neg p21]
  have p22 : ¬ Nat.Prime 22 := by norm_num
  have c23 : count Nat.Prime 23 = 8 := by rw [count_succ, c22, if_neg p22]
  have p23 : Nat.Prime 23 := by norm_num
  have c24 : count Nat.Prime 24 = 9 := by rw [count_succ, c23, if_pos p23]
  have p24 : ¬ Nat.Prime 24 := by norm_num
  have c25 : count Nat.Prime 25 = 9 := by rw [count_succ, c24, if_neg p24]
  have p25 : ¬ Nat.Prime 25 := by norm_num
  have c26 : count Nat.Prime 26 = 9 := by rw [count_succ, c25, if_neg p25]
  have p26 : ¬ Nat.Prime 26 := by norm_num
  have c27 : count Nat.Prime 27 = 9 := by rw [count_succ, c26, if_neg p26]
  have p27 : ¬ Nat.Prime 27 := by norm_num
  have c28 : count Nat.Prime 28 = 9 := by rw [count_succ, c27, if_neg p27]
  have p28 : ¬ Nat.Prime 28 := by norm_num
  have c29 : count Nat.Prime 29 = 9 := by rw [count_succ, c28, if_neg p28]
  have p29 : Nat.Prime 29 := by norm_num
  have c30 : count Nat.Prime 30 = 10 := by rw [count_succ, c29, if_pos p29]
  have p30 : ¬ Nat.Prime 30 := by norm_num
  have c31 : count Nat.Prime 31 = 10 := by rw [count_succ, c30, if_neg p30]
  have p31 : Nat.Prime 31 := by norm_num
  have c32 : count Nat.Prime 32 = 11 := by rw [count_succ, c31, if_pos p31]
  have p32 : ¬ Nat.Prime 32 := by norm_num
  have c33 : count Nat.Prime 33 = 11 := by rw [count_succ, c32, if_neg p32]
  have p33 : ¬ Nat.Prime 33 := by norm_num
  have c34 : count Nat.Prime 34 = 11 := by rw [count_succ, c33, if_neg p33]
  have p34 : ¬ Nat.Prime 34 := by norm_num
  have c35 : count Nat.Prime 35 = 11 := by rw [count_succ, c34, if_neg p34]
  have p35 : ¬ Nat.Prime 35 := by norm_num
  have c36 : count Nat.Prime 36 = 11 := by rw [count_succ, c35, if_neg p35]
  have p36 : ¬ Nat.Prime 36 := by norm_num
  have c37 : count Nat.Prime 37 = 11 := by rw [count_succ, c36, if_neg p36]
  have p37 : Nat.Prime 37 := by norm_num
  have c38 : count Nat.Prime 38 = 12 := by rw [count_succ, c37, if_pos p37]
  have p38 : ¬ Nat.Prime 38 := by norm_num
  have c39 : count Nat.Prime 39 = 12 := by rw [count_succ, c38, if_neg p38]
  have p39 : ¬ Nat.Prime 39 := by norm_num
  have c40 : count Nat.Prime 40 = 12 := by rw [count_succ, c39, if_neg p39]
  have p40 : ¬ Nat.Prime 40 := by norm_num
  have c41 : count Nat.Prime 41 = 12 := by rw [count_succ, c40, if_neg p40]
  have p41 : Nat.Prime 41 := by norm_num
  have c42 : count Nat.Prime 42 = 13 := by rw [count_succ, c41, if_pos p41]
  have p42 : ¬ Nat.Prime 42 := by norm_num
  have c43 : count Nat.Prime 43 = 13 := by rw [count_succ, c42, if_neg p42]
  have p43 : Nat.Prime 43 := by norm_num
  have c44 : count Nat.Prime 44 = 14 := by rw [count_succ, c43, if_pos p43]
  have p44 : ¬ Nat.Prime 44 := by norm_num
  have c45 : count Nat.Prime 45 = 14 := by rw [count_succ, c44, if_neg p44]
  have p45 : ¬ Nat.Prime 45 := by norm_num
  have c46 : count Nat.Prime 46 = 14 := by rw [count_succ, c45, if_neg p45]
  have p46 : ¬ Nat.Prime 46 := by norm_num
  have c47 : count Nat.Prime 47 = 14 := by rw [count_succ, c46, if_neg p46]
  have p47 : Nat.Prime 47 := by norm_num
  have c48 : count Nat.Prime 48 = 15 := by rw [count_succ, c47, if_pos p47]
  have p48 : ¬ Nat.Prime 48 := by norm_num
  have c49 : count Nat.Prime 49 = 15 := by rw [count_succ, c48, if_neg p48]
  have p49 : ¬ Nat.Prime 49 := by norm_num
  have c50 : count Nat.Prime 50 = 15 := by rw [count_succ, c49, if_neg p49]
  have p50 : ¬ Nat.Prime 50 := by norm_num
  have c51 : count Nat.Prime 51 = 15 := by rw [count_succ, c50, if_neg p50]
  have p51 : ¬ Nat.Prime 51 := by norm_num
  have c52 : count Nat.Prime 52 = 15 := by rw [count_succ, c51, if_neg p51]
  have p52 : ¬ Nat.Prime 52 := by norm_num
  have c53 : count Nat.Prime 53 = 15 := by rw [count_succ, c52, if_neg p52]
  have p53 : Nat.Prime 53 := by norm_num
  have c54 : count Nat.Prime 54 = 16 := by rw [count_succ, c53, if_pos p53]
  have p54 : ¬ Nat.Prime 54 := by norm_num
  have c55 : count Nat.Prime 55 = 16 := by rw [count_succ, c54, if_neg p54]
  have p55 : ¬ Nat.Prime 55 := by norm_num
  have c56 : count Nat.Prime 56 = 16 := by rw [count_succ, c55, if_neg p55]
  have p56 : ¬ Nat.Prime 56 := by norm_num
  have c57 : count Nat.Prime 57 = 16 := by rw [count_succ, c56, if_neg p56]
  have p57 : ¬ Nat.Prime 57 := by norm_num
  have c58 : count Nat.Prime 58 = 16 := by rw [count_succ, c57, if_neg p57]
  have p58 : ¬ Nat.Prime 58 := by norm_num
  have c59 : count Nat.Prime 59 = 16 := by rw [count_succ, c58, if_neg p58]
  have p59 : Nat.Prime 59 := by norm_num
  have c60 : count Nat.Prime 60 = 17 := by rw [count_succ, c59, if_pos p59]
  have p60 : ¬ Nat.Prime 60 := by norm_num
  have c61 : count Nat.Prime 61 = 17 := by rw [count_succ, c60, if_neg p60]
  have p61 : Nat.Prime 61 := by norm_num
  have c62 : count Nat.Prime 62 = 18 := by rw [count_succ, c61, if_pos p61]
  have p62 : ¬ Nat.Prime 62 := by norm_num
  have c63 : count Nat.Prime 63 = 18 := by rw [count_succ, c62, if_neg p62]
  have p63 : ¬ Nat.Prime 63 := by norm_num
  have c64 : count Nat.Prime 64 = 18 := by rw [count_succ, c63, if_neg p63]
  have p64 : ¬ Nat.Prime 64 := by norm_num
  have c65 : count Nat.Prime 65 = 18 := by rw [count_succ, c64, if_neg p64]
  have p65 : ¬ Nat.Prime 65 := by norm_num
  have c66 : count Nat.Prime 66 = 18 := by rw [count_succ, c65, if_neg p65]
  have p66 : ¬ Nat.Prime 66 := by norm_num
  have c67 : count Nat.Prime 67 = 18 := by rw [count_succ, c66, if_neg p66]
  have p67 : Nat.Prime 67 := by norm_num
  have c68 : count Nat.Prime 68 = 19 := by rw [count_succ, c67, if_pos p67]
  have p68 : ¬ Nat.Prime 68 := by norm_num
  have c69 : count Nat.Prime 69 = 19 := by rw [count_succ, c68, if_neg p68]
  have p69 : ¬ Nat.Prime 69 := by norm_num
  have c70 : count Nat.Prime 70 = 19 := by rw [count_succ, c69, if_neg p69]
  have p70 : ¬ Nat.Prime 70 := by norm_num
  have c71 : count Nat.Prime 71 = 19 := by rw [count_succ, c70, if_neg p70]
  have p71 : Nat.Prime 71 := by norm_num
  have c72 : count Nat.Prime 72 = 20 := by rw [count_succ, c71, if_pos p71]
  have p72 : ¬ Nat.Prime 72 := by norm_num
  have c73 : count Nat.Prime 73 = 20 := by rw [count_succ, c72, if_neg p72]
  have p73 : Nat.Prime 73 := by norm_num
  have c74 : count Nat.Prime 74 = 21 := by rw [count_succ, c73, if_pos p73]
  have p74 : ¬ Nat.Prime 74 := by norm_num
  have c75 : count Nat.Prime 75 = 21 := by rw [count_succ, c74, if_neg p74]
  have p75 : ¬ Nat.Prime 75 := by norm_num
  have c76 : count Nat.Prime 76 = 21 := by rw [count_succ, c75, if_neg p75]
  have p76 : ¬ Nat.Prime 76 := by norm_num
  have c77 : count Nat.Prime 77 = 21 := by rw [count_succ, c76, if_neg p76]
  have p77 : ¬ Nat.Prime 77 := by norm_num
  have c78 : count Nat.Prime 78 = 21 := by rw [count_succ, c77, if_neg p77]
  have p78 : ¬ Nat.Prime 78 := by norm_num
  have c79 : count Nat.Prime 79 = 21 := by rw [count_succ, c78, if_neg p78]
  have p79 : Nat.Prime 79 := by norm_num
  have c80 : count Nat.Prime 80 = 22 := by rw [count_succ, c79, if_pos p79]
  have p80 : ¬ Nat.Prime 80 := by norm_num
  have c81 : count Nat.Prime 81 = 22 := by rw [count_succ, c80, if_neg p80]
  have p81 : ¬ Nat.Prime 81 := by norm_num
  have c82 : count Nat.Prime 82 = 22 := by rw [count_succ, c81, if_neg p81]
  have p82 : ¬ Nat.Prime 82 := by norm_num
  have c83 : count Nat.Prime 83 = 22 := by rw [count_succ, c82, if_neg p82]
  have p83 : Nat.Prime 83 := by norm_num
  have c84 : count Nat.Prime 84 = 23 := by rw [count_succ, c83, if_pos p83]
  have p84 : ¬ Nat.Prime 84 := by norm_num
  have c85 : count Nat.Prime 85 = 23 := by rw [count_succ, c84, if_neg p84]
  have p85 : ¬ Nat.Prime 85 := by norm_num
  have c86 : count Nat.Prime 86 = 23 := by rw [count_succ, c85, if_neg p85]
  have p86 : ¬ Nat.Prime 86 := by norm_num
  have c87 : count Nat.Prime 87 = 23 := by rw [count_succ, c86, if_neg p86]
  have p87 : ¬ Nat.Prime 87 := by norm_num
  have c88 : count Nat.Prime 88 = 23 := by rw [count_succ, c87, if_neg p87]
  have p88 : ¬ Nat.Prime 88 := by norm_num
  have c89 : count Nat.Prime 89 = 23 := by rw [count_succ, c88, if_neg p88]
  have p89 : Nat.Prime 89 := by norm_num
  have c90 : count Nat.Prime 90 = 24 := by rw [count_succ, c89, if_pos p89]
  have p90 : ¬ Nat.Prime 90 := by norm_num
  have c91 : count Nat.Prime 91 = 24 := by rw [count_succ, c90, if_neg p90]
  have p91 : ¬ Nat.Prime 91 := by norm_num
  have c92 : count Nat.Prime 92 = 24 := by rw [count_succ, c91, if_neg p91]
  have p92 : ¬ Nat.Prime 92 := by norm_num
  have c93 : count Nat.Prime 93 = 24 := by rw [count_succ, c92, if_neg p92]
  have p93 : ¬ Nat.Prime 93 := by norm_num
  have c94 : count Nat.Prime 94 = 24 := by rw [count_succ, c93, if_neg p93]
  have p94 : ¬ Nat.Prime 94 := by norm_num
  have c95 : count Nat.Prime 95 = 24 := by rw [count_succ, c94, if_neg p94]
  have p95 : ¬ Nat.Prime 95 := by norm_num
  have c96 : count Nat.Prime 96 = 24 := by rw [count_succ, c95, if_neg p95]
  have p96 : ¬ Nat.Prime 96 := by norm_num
  have c97 : count Nat.Prime 97 = 24 := by rw [count_succ, c96, if_neg p96]
  have p97 : Nat.Prime 97 := by norm_num
  have c98 : count Nat.Prime 98 = 25 := by rw [count_succ, c97, if_pos p97]
  have p98 : ¬ Nat.Prime 98 := by norm_num
  have c99 : count Nat.Prime 99 = 25 := by rw [count_succ, c98, if_neg p98]
  have p99 : ¬ Nat.Prime 99 := by norm_num
  have c100 : count Nat.Prime 100 = 25 := by rw [count_succ, c99, if_neg p99]
  have p100 : ¬ Nat.Prime 100 := by norm_num
  have c101 : count Nat.Prime 101 = 25 := by rw [count_succ, c100, if_neg p100]
  have p101 : Nat.Prime 101 := by norm_num
  have c102 : count Nat.Prime 102 = 26 := by rw [count_succ, c101, if_pos p101]
  have p102 : ¬ Nat.Prime 102 := by norm_num
  have c103 : count Nat.Prime 103 = 26 := by rw [count_succ, c102, if_neg p102]
  have p103 : Nat.Prime 103 := by norm_num
  have c104 : count Nat.Prime 104 = 27 := by rw [count_succ, c103, if_pos p103]
  have p104 : ¬ Nat.Prime 104 := by norm_num
  have c105 : count Nat.Prime 105 = 27 := by rw [count_succ, c104, if_neg p104]
  have p105 : ¬ Nat.Prime 105 := by norm_num
  have c106 : count Nat.Prime 106 = 27 := by rw [count_succ, c105, if_neg p105]
  have p106 : ¬ Nat.Prime 106 := by norm_num
  have c107 : count Nat.Prime 107 = 27 := by rw [count_succ, c106, if_neg p106]
  have p107 : Nat.Prime 107 := by norm_num
  have c108 : count Nat.Prime 108 = 28 := by rw [count_succ, c107, if_pos p107]
  have p108 : ¬ Nat.Prime 108 := by norm_num
  have c109 : count Nat.Prime 109 = 28 := by rw [count_succ, c108, if_neg p108]
  have p109 : Nat.Prime 109 := by norm_num
  have c110 : count Nat.Prime 110 = 29 := by rw [count_succ, c109, if_pos p109]
  have p110 : ¬ Nat.Prime 110 := by norm_num
  have c111 : count Nat.Prime 111 = 29 := by rw [count_succ, c110, if_neg p110]
  have p111 : ¬ Nat.Prime 111 := by norm_num
  have c112 : count Nat.Prime 112 = 29 := by rw [count_succ, c111, if_neg p111]
  have p112 : ¬ Nat.Prime 112 := by norm_num
  have c113 : count Nat.Prime 113 = 29 := by rw [count_succ, c112, if_neg p112]
  have p113 : Nat.Prime 113 := by norm_num
  have c114 : count Nat.Prime 114 = 30 := by rw [count_succ, c113, if_pos p113]
  have p114 : ¬ Nat.Prime 114 := by norm_num
  have c115 : count Nat.Prime 115 = 30 := by rw [count_succ, c114, if_neg p114]
  have p115 : ¬ Nat.Prime 115 := by norm_num
  have c116 : count Nat.Prime 116 = 30 := by rw [count_succ, c115, if_neg p115]
  have p116 : ¬ Nat.Prime 116 := by norm_num
  have c117 : count Nat.Prime 117 = 30 := by rw [count_succ, c116, if_neg p116]
  have p117 : ¬ Nat.Prime 117 := by norm_num
  have c118 : count Nat.Prime 118 = 30 := by rw [count_succ, c117, if_neg p117]
  have p118 : ¬ Nat.Prime 118 := by norm_num
  have c119 : count Nat.Prime 119 = 30 := by rw [count_succ, c118, if_neg p118]
  have p119 : ¬ Nat.Prime 119 := by norm_num
  have c120 : count Nat.Prime 120 = 30 := by rw [count_succ, c119, if_neg p119]
  have p120 : ¬ Nat.Prime 120 := by norm_num
  have c121 : count Nat.Prime 121 = 30 := by rw [count_succ, c120, if_neg p120]
  have p121 : ¬ Nat.Prime 121 := by norm_num
  have c122 : count Nat.Prime 122 = 30 := by rw [count_succ, c121, if_neg p121]
  have p122 : ¬ Nat.Prime 122 := by norm_num
  have c123 : count Nat.Prime 123 = 30 := by rw [count_succ, c122, if_neg p122]
  have p123 : ¬ Nat.Prime 123 := by norm_num
  have c124 : count Nat.Prime 124 = 30 := by rw [count_succ, c123, if_neg p123]
  have p124 : ¬ Nat.Prime 124 := by norm_num
  have c125 : count Nat.Prime 125 = 30 := by rw [count_succ, c124, if_neg p124]
  have p125 : ¬ Nat.Prime 125 := by norm_num
  have c126 : count Nat.Prime 126 = 30 := by rw [count_succ, c125, if_neg p125]
  have p126 : ¬ Nat.Prime 126 := by norm_num
  have c127 : count Nat.Prime 127 = 30 := by rw [count_succ, c126, if_neg p126]
  have p127 : Nat.Prime 127 := by norm_num
  have c128 : count Nat.Prime 128 = 31 := by rw [count_succ, c127, if_pos p127]
  have p128 : ¬ Nat.Prime 128 := by norm_num
  have c129 : count Nat.Prime 129 = 31 := by rw [count_succ, c128, if_neg p128]
  have p129 : ¬ Nat.Prime 129 := by norm_num
  have c130 : count Nat.Prime 130 = 31 := by rw [count_succ, c129, if_neg p129]
  have p130 : ¬ Nat.Prime 130 := by norm_num
  have c131 : count Nat.Prime 131 = 31 := by rw [count_succ, c130, if_neg p130]
  have p131 : Nat.Prime 131 := by norm_num
  have c132 : count Nat.Prime 132 = 32 := by rw [count_succ, c131, if_pos p131]
  have p132 : ¬ Nat.Prime 132 := by norm_num
  have c133 : count Nat.Prime 133 = 32 := by rw [count_succ, c132, if_neg p132]
  have p133 : ¬ Nat.Prime 133 := by norm_num
  have c134 : count Nat.Prime 134 = 32 := by rw [count_succ, c133, if_neg p133]
  have p134 : ¬ Nat.Prime 134 := by norm_num
  have c135 : count Nat.Prime 135 = 32 := by rw [count_succ, c134, if_neg p134]
  have p135 : ¬ Nat.Prime 135 := by norm_num
  have c136 : count Nat.Prime 136 = 32 := by rw [count_succ, c135, if_neg p135]
  have p136 : ¬ Nat.Prime 136 := by norm_num
  have c137 : count Nat.Prime 137 = 32 := by rw [count_succ, c136, if_neg p136]
  have p137 : Nat.Prime 137 := by norm_num
  have c138 : count Nat.Prime 138 = 33 := by rw [count_succ, c137, if_pos p137]
  have p138 : ¬ Nat.Prime 138 := by norm_num
  have c139 : count Nat.Prime 139 = 33 := by rw [count_succ, c138, if_neg p138]
  have p139 : Nat.Prime 139 := by norm_num
  have c140 : count Nat.Prime 140 = 34 := by rw [count_succ, c139, if_pos p139]
  have p140 : ¬ Nat.Prime 140 := by norm_num
  have c141 : count Nat.Prime 141 = 34 := by rw [count_succ, c140, if_neg p140]
  have p141 : ¬ Nat.Prime 141 := by norm_num
  have c142 : count Nat.Prime 142 = 34 := by rw [count_succ, c141, if_neg p141]
  have p142 : ¬ Nat.Prime 142 := by norm_num
  have c143 : count Nat.Prime 143 = 34 := by rw [count_succ, c142, if_neg p142]
  have p143 : ¬ Nat.Prime 143 := by norm_num
  have c144 : count Nat.Prime 144 = 34 := by rw [count_succ, c143, if_neg p143]
  have p144 : ¬ Nat.Prime 144 := by norm_num
  have c145 : count Nat.Prime 145 = 34 := by rw [count_succ, c144, if_neg p144]
  have p145 : ¬ Nat.Prime 145 := by norm_num
  have c146 : count Nat.Prime 146 = 34 := by rw [count_succ, c145, if_neg p145]
  have p146 : ¬ Nat.Prime 146 := by norm_num
  have c147 : count Nat.Prime 147 = 34 := by rw [count_succ, c146, if_neg p146]
  have p147 : ¬ Nat.Prime 147 := by norm_num
  have c148 : count Nat.Prime 148 = 34 := by rw [count_succ, c147, if_neg p147]
  have p148 : ¬ Nat.Prime 148 := by norm_num
  have c149 : count Nat.Prime 149 = 34 := by rw [count_succ, c148, if_neg p148]
  have p149 : Nat.Prime 149 := by norm_num
  have c150 : count Nat.Prime 150 = 35 := by rw [count_succ, c149, if_pos p149]
  have p150 : ¬ Nat.Prime 150 := by norm_num
  have c151 : count Nat.Prime 151 = 35 := by rw [count_succ, c150, if_neg p150]
  have p151 : Nat.Prime 151 := by norm_num
  have c152 : count Nat.Prime 152 = 36 := by rw [count_succ, c151, if_pos p151]
  have p152 : ¬ Nat.Prime 152 := by norm_num
  have c153 : count Nat.Prime 153 = 36 := by rw [count_succ, c152, if_neg p152]
  have p153 : ¬ Nat.Prime 153 := by norm_num
  have c154 : count Nat.Prime 154 = 36 := by rw [count_succ, c153, if_neg p153]
  have p154 : ¬ Nat.Prime 154 := by norm_num
  have c155 : count Nat.Prime 155 = 36 := by rw [count_succ, c154, if_neg p154]
  have p155 : ¬ Nat.Prime 155 := by norm_num
  have c156 : count Nat.Prime 156 = 36 := by rw [count_succ, c155, if_neg p155]
  have p156 : ¬ Nat.Prime 156 := by norm_num
  have c157 : count Nat.Prime 157 = 36 := by rw [count_succ, c156, if_neg p156]
  have p157 : Nat.Prime 157 := by norm_num
  have c158 : count Nat.Prime 158 = 37 := by rw [count_succ, c157, if_pos p157]
  have p158 : ¬ Nat.Prime 158 := by norm_num
  have c159 : count Nat.Prime 159 = 37 := by rw [count_succ, c158, if_neg p158]
  have p159 : ¬ Nat.Prime 159 := by norm_num
  have c160 : count Nat.Prime 160 = 37 := by rw [count_succ, c159, if_neg p159]
  have p160 : ¬ Nat.Prime 160 := by norm_num
  have c161 : count Nat.Prime 161 = 37 := by rw [count_succ, c160, if_neg p160]
  have p161 : ¬ Nat.Prime 161 := by norm_num
  have c162 : count Nat.Prime 162 = 37 := by rw [count_succ, c161, if_neg p161]
  have p162 : ¬ Nat.Prime 162 := by norm_num
  have c163 : count Nat.Prime 163 = 37 := by rw [count_succ, c162, if_neg p162]
  have p163 : Nat.Prime 163 := by norm_num
  have c164 : count Nat.Prime 164 = 38 := by rw [count_succ, c163, if_pos p163]
  have p164 : ¬ Nat.Prime 164 := by norm_num
  have c165 : count Nat.Prime 165 = 38 := by rw [count_succ, c164, if_neg p164]
  have p165 : ¬ Nat.Prime 165 := by norm_num
  have c166 : count Nat.Prime 166 = 38 := by rw [count_succ, c165, if_neg p165]
  have p166 : ¬ Nat.Prime 166 := by norm_num
  have c167 : count Nat.Prime 167 = 38 := by rw [count_succ, c166, if_neg p166]
  have p167 : Nat.Prime 167 := by norm_num
  have c168 : count Nat.Prime 168 = 39 := by rw [count_succ, c167, if_pos p167]
  have p168 : ¬ Nat.Prime 168 := by norm_num
  have c169 : count Nat.Prime 169 = 39 := by rw [count_succ, c168, if_neg p168]
  have p169 : ¬ Nat.Prime 169 := by norm_num
  have c170 : count Nat.Prime 170 = 39 := by rw [count_succ, c169, if_neg p169]
  have p170 : ¬ Nat.Prime 170 := by norm_num
  have c171 : count Nat.Prime 171 = 39 := by rw [count_succ, c170, if_neg p170]
  have p171 : ¬ Nat.Prime 171 := by norm_num
  have c172 : count Nat.Prime 172 = 39 := by rw [count_succ, c171, if_neg p171]
  have p172 : ¬ Nat.Prime 172 := by norm_num
  have c173 : count Nat.Prime 173 = 39 := by rw [count_succ, c172, if_neg p172]
  have p173 : Nat.Prime 173 := by norm_num
  have c174 : count Nat.Prime 174 = 40 := by rw [count_succ, c173, if_pos p173]
  have p174 : ¬ Nat.Prime 174 := by norm_num
  have c175 : count Nat.Prime 175 = 40 := by rw [count_succ, c174, if_neg p174]
  have p175 : ¬ Nat.Prime 175 := by norm_num
  have c176 : count Nat.Prime 176 = 40 := by rw [count_succ, c175, if_neg p175]
  have p176 : ¬ Nat.Prime 176 := by norm_num
  have c177 : count Nat.Prime 177 = 40 := by rw [count_succ, c176, if_neg p176]
  have p177 : ¬ Nat.Prime 177 := by norm_num
  have c178 : count Nat.Prime 178 = 40 := by rw [count_succ, c177, if_neg p177]
  have p178 : ¬ Nat.Prime 178 := by norm_num
  have c179 : count Nat.Prime 179 = 40 := by rw [count_succ, c178, if_neg p178]
  have p179 : Nat.Prime 179 := by norm_num
  have c180 : count Nat.Prime 180 = 41 := by rw [count_succ, c179, if_pos p179]
  have p180 : ¬ Nat.Prime 180 := by norm_num
  have c181 : count Nat.Prime 181 = 41 := by rw [count_succ, c180, if_neg p180]
  have p181 : Nat.Prime 181 := by norm_num
  have c182 : count Nat.Prime 182 = 42 := by rw [count_succ, c181, if_pos p181]
  have p182 : ¬ Nat.Prime 182 := by norm_num
  have c183 : count Nat.Prime 183 = 42 := by rw [count_succ, c182, if_neg p182]
  have p183 : ¬ Nat.Prime 183 := by norm_num
  have c184 : count Nat.Prime 184 = 42 := by rw [count_succ, c183, if_neg p183]
  have p184 : ¬ Nat.Prime 184 := by norm_num
  have c185 : count Nat.Prime 185 = 42 := by rw [count_succ, c184, if_neg p184]
  have p185 : ¬ Nat.Prime 185 := by norm_num
  have c186 : count Nat.Prime 186 = 42 := by rw [count_succ, c185, if_neg p185]
  have p186 : ¬ Nat.Prime 186 := by norm_num
  have c187 : count Nat.Prime 187 = 42 := by rw [count_succ, c186, if_neg p186]
  have p187 : ¬ Nat.Prime 187 := by norm_num
  have c188 : count Nat.Prime 188 = 42 := by rw [count_succ, c187, if_neg p187]
  have p188 : ¬ Nat.Prime 188 := by norm_num
  have c189 : count Nat.Prime 189 = 42 := by rw [count_succ, c188, if_neg p188]
  have p189 : ¬ Nat.Prime 189 := by norm_num
  have c190 : count Nat.Prime 190 = 42 := by rw [count_succ, c189, if_neg p189]
  have p190 : ¬ Nat.Prime 190 := by norm_num
  have c191 : count Nat.Prime 191 = 42 := by rw [count_succ, c190, if_neg p190]
  have p191 : Nat.Prime 191 := by norm_num
  have c192 : count Nat.Prime 192 = 43 := by rw [count_succ, c191, if_pos p191]
  have p192 : ¬ Nat.Prime 192 := by norm_num
  have c193 : count Nat.Prime 193 = 43 := by rw [count_succ, c192, if_neg p192]
  have p193 : Nat.Prime 193 := by norm_num
  have c194 : count Nat.Prime 194 = 44 := by rw [count_succ, c193, if_pos p193]
  have p194 : ¬ Nat.Prime 194 := by norm_num
  have c195 : count Nat.Prime 195 = 44 := by rw [count_succ, c194, if_neg p194]
  have p195 : ¬ Nat.Prime 195 := by norm_num
  have c196 : count Nat.Prime 196 = 44 := by rw [count_succ, c195, if_neg p195]
  have p196 : ¬ Nat.Prime 196 := by norm_num
  have c197 : count Nat.Prime 197 = 44 := by rw [count_succ, c196, if_neg p196]
  have p197 : Nat.Prime 197 := by norm_num
  have c198 : count Nat.Prime 198 = 45 := by rw [count_succ, c197, if_pos p197]
  have p198 : ¬ Nat.Prime 198 := by norm_num
  have c199 : count Nat.Prime 199 = 45 := by rw [count_succ, c198, if_neg p198]
  have p199 : Nat.Prime 199 := by norm_num
  have c200 : count Nat.Prime 200 = 46 := by rw [count_succ, c199, if_pos p199]
  have p200 : ¬ Nat.Prime 200 := by norm_num
  have c201 : count Nat.Prime 201 = 46 := by rw [count_succ, c200, if_neg p200]
  have p201 : ¬ Nat.Prime 201 := by norm_num
  have c202 : count Nat.Prime 202 = 46 := by rw [count_succ, c201, if_neg p201]
  have p202 : ¬ Nat.Prime 202 := by norm_num
  have c203 : count Nat.Prime 203 = 46 := by rw [count_succ, c202, if_neg p202]
  have p203 : ¬ Nat.Prime 203 := by norm_num
  have c204 : count Nat.Prime 204 = 46 := by rw [count_succ, c203, if_neg p203]
  have p204 : ¬ Nat.Prime 204 := by norm_num
  have c205 : count Nat.Prime 205 = 46 := by rw [count_succ, c204, if_neg p204]
  have p205 : ¬ Nat.Prime 205 := by norm_num
  have c206 : count Nat.Prime 206 = 46 := by rw [count_succ, c205, if_neg p205]
  have p206 : ¬ Nat.Prime 206 := by norm_num
  have c207 : count Nat.Prime 207 = 46 := by rw [count_succ, c206, if_neg p206]
  have p207 : ¬ Nat.Prime 207 := by norm_num
  have c208 : count Nat.Prime 208 = 46 := by rw [count_succ, c207, if_neg p207]
  have p208 : ¬ Nat.Prime 208 := by norm_num
  have c209 : count Nat.Prime 209 = 46 := by rw [count_succ, c208, if_neg p208]
  have p209 : ¬ Nat.Prime 209 := by norm_num
  have c210 : count Nat.Prime 210 = 46 := by rw [count_succ, c209, if_neg p209]
  have p210 : ¬ Nat.Prime 210 := by norm_num
  have c211 : count Nat.Prime 211 = 46 := by rw [count_succ, c210, if_neg p210]
  have p211 : Nat.Prime 211 := by norm_num
  have c212 : count Nat.Prime 212 = 47 := by rw [count_succ, c211, if_pos p211]
  have p212 : ¬ Nat.Prime 212 := by norm_num
  have c213 : count Nat.Prime 213 = 47 := by rw [count_succ, c212, if_neg p212]
  have p213 : ¬ Nat.Prime 213 := by norm_num
  have c214 : count Nat.Prime 214 = 47 := by rw [count_succ, c213, if_neg p213]
  have p214 : ¬ Nat.Prime 214 := by norm_num
  have c215 : count Nat.Prime 215 = 47 := by rw [count_succ, c214, if_neg p214]
  have p215 : ¬ Nat.Prime 215 := by norm_num
  have c216 : count Nat.Prime 216 = 47 := by rw [count_succ, c215, if_neg p215]
  have p216 : ¬ Nat.Prime 216 := by norm_num
  have c217 : count Nat.Prime 217 = 47 := by rw [count_succ, c216, if_neg p216]
  have p217 : ¬ Nat.Prime 217 := by norm_num
  have c218 : count Nat.Prime 218 = 47 := by rw [count_succ, c217, if_neg p217]
  have p218 : ¬ Nat.Prime 218 := by norm_num
  have c219 : count Nat.Prime 219 = 47 := by rw [count_succ, c218, if_neg p218]
  have p219 : ¬ Nat.Prime 219 := by norm_num
  have c220 : count Nat.Prime 220 = 47 := by rw [count_succ, c219, if_neg p219]
  have p220 : ¬ Nat.Prime 220 := by norm_num
  have c221 : count Nat.Prime 221 = 47 := by rw [count_succ, c220, if_neg p220]
  have p221 : ¬ Nat.Prime 221 := by norm_num
  have c222 : count Nat.Prime 222 = 47 := by rw [count_succ, c221, if_neg p221]
  have p222 : ¬ Nat.Prime 222 := by norm_num
  have c223 : count Nat.Prime 223 = 47 := by rw [count_succ, c222, if_neg p222]
  have p223 : Nat.Prime 223 := by norm_num
  have c224 : count Nat.Prime 224 = 48 := by rw [count_succ, c223, if_pos p223]
  have p224 : ¬ Nat.Prime 224 := by norm_num
  have c225 : count Nat.Prime 225 = 48 := by rw [count_succ, c224, if_neg p224]
  have p225 : ¬ Nat.Prime 225 := by norm_num
  have c226 : count Nat.Prime 226 = 48 := by rw [count_succ, c225, if_neg p225]
  have p226 : ¬ Nat.Prime 226 := by norm_num
  have c227 : count Nat.Prime 227 = 48 := by rw [count_succ, c226, if_neg p226]
  have p227 : Nat.Prime 227 := by norm_num
  have c228 : count Nat.Prime 228 = 49 := by rw [count_succ, c227, if_pos p227]
  have p228 : ¬ Nat.Prime 228 := by norm_num
  have c229 : count Nat.Prime 229 = 49 := by rw [count_succ, c228, if_neg p228]
  have p229 : Nat.Prime 229 := by norm_num
  have c230 : count Nat.Prime 230 = 50 := by rw [count_succ, c229, if_pos p229]
  have p230 : ¬ Nat.Prime 230 := by norm_num
  have c231 : count Nat.Prime 231 = 50 := by rw [count_succ, c230, if_neg p230]
  have p231 : ¬ Nat.Prime 231 := by norm_num
  have c232 : count Nat.Prime 232 = 50 := by rw [count_succ, c231, if_neg p231]
  have p232 : ¬ Nat.Prime 232 := by norm_num
  have c233 : count Nat.Prime 233 = 50 := by rw [count_succ, c232, if_neg p232]
  have p233 : Nat.Prime 233 := by norm_num
  have c234 : count Nat.Prime 234 = 51 := by rw [count_succ, c233, if_pos p233]
  have p234 : ¬ Nat.Prime 234 := by norm_num
  have c235 : count Nat.Prime 235 = 51 := by rw [count_succ, c234, if_neg p234]
  have p235 : ¬ Nat.Prime 235 := by norm_num
  have c236 : count Nat.Prime 236 = 51 := by rw [count_succ, c235, if_neg p235]
  have p236 : ¬ Nat.Prime 236 := by norm_num
  have c237 : count Nat.Prime 237 = 51 := by rw [count_succ, c236, if_neg p236]
  have p237 : ¬ Nat.Prime 237 := by norm_num
  have c238 : count Nat.Prime 238 = 51 := by rw [count_succ, c237, if_neg p237]
  have p238 : ¬ Nat.Prime 238 := by norm_num
  have c239 : count Nat.Prime 239 = 51 := by rw [count_succ, c238, if_neg p238]
  have p239 : Nat.Prime 239 := by norm_num
  have c240 : count Nat.Prime 240 = 52 := by rw [count_succ, c239, if_pos p239]
  have p240 : ¬ Nat.Prime 240 := by norm_num
  have c241 : count Nat.Prime 241 = 52 := by rw [count_succ, c240, if_neg p240]
  have p241 : Nat.Prime 241 := by norm_num
  have c242 : count Nat.Prime 242 = 53 := by rw [count_succ, c241, if_pos p241]
  have p242 : ¬ Nat.Prime 242 := by norm_num
  have c243 : count Nat.Prime 243 = 53 := by rw [count_succ, c242, if_neg p242]
  have p243 : ¬ Nat.Prime 243 := by norm_num
  have c244 : count Nat.Prime 244 = 53 := by rw [count_succ, c243, if_neg p243]
  have p244 : ¬ Nat.Prime 244 := by norm_num
  have c245 : count Nat.Prime 245 = 53 := by rw [count_succ, c244, if_neg p244]
  have p245 : ¬ Nat.Prime 245 := by norm_num
  have c246 : count Nat.Prime 246 = 53 := by rw [count_succ, c245, if_neg p245]
  have p246 : ¬ Nat.Prime 246 := by norm_num
  have c247 : count Nat.Prime 247 = 53 := by rw [count_succ, c246, if_neg p246]
  have p247 : ¬ Nat.Prime 247 := by norm_num
  have c248 : count Nat.Prime 248 = 53 := by rw [count_succ, c247, if_neg p247]
  have p248 : ¬ Nat.Prime 248 := by norm_num
  have c249 : count Nat.Prime 249 = 53 := by rw [count_succ, c248, if_neg p248]
  have p249 : ¬ Nat.Prime 249 := by norm_num
  have c250 : count Nat.Prime 250 = 53 := by rw [count_succ, c249, if_neg p249]
  have p250 : ¬ Nat.Prime 250 := by norm_num
  have c251 : count Nat.Prime 251 = 53 := by rw [count_succ, c250, if_neg p250]
  have p251 : Nat.Prime 251 := by norm_num
  have c252 : count Nat.Prime 252 = 54 := by rw [count_succ, c251, if_pos p251]
  have p252 : ¬ Nat.Prime 252 := by norm_num
  have c253 : count Nat.Prime 253 = 54 := by rw [count_succ, c252, if_neg p252]
  have p253 : ¬ Nat.Prime 253 := by norm_num
  have c254 : count Nat.Prime 254 = 54 := by rw [count_succ, c253, if_neg p253]
  have p254 : ¬ Nat.Prime 254 := by norm_num
  have c255 : count Nat.Prime 255 = 54 := by rw [count_succ, c254, if_neg p254]
  have p255 : ¬ Nat.Prime 255 := by norm_num
  have c256 : count Nat.Prime 256 = 54 := by rw [count_succ, c255, if_neg p255]
  have p256 : ¬ Nat.Prime 256 := by norm_num
  have c257 : count Nat.Prime 257 = 54 := by rw [count_succ, c256, if_neg p256]
  have p257 : Nat.Prime 257 := by norm_num
  have c258 : count Nat.Prime 258 = 55 := by rw [count_succ, c257, if_pos p257]
  have p258 : ¬ Nat.Prime 258 := by norm_num
  have c259 : count Nat.Prime 259 = 55 := by rw [count_succ, c258, if_neg p258]
  have p259 : ¬ Nat.Prime 259 := by norm_num
  have c260 : count Nat.Prime 260 = 55 := by rw [count_succ, c259, if_neg p259]
  have p260 : ¬ Nat.Prime 260 := by norm_num
  have c261 : count Nat.Prime 261 = 55 := by rw [count_succ, c260, if_neg p260]
  have p261 : ¬ Nat.Prime 261 := by norm_num
  have c262 : count Nat.Prime 262 = 55 := by rw [count_succ, c261, if_neg p261]
  have p262 : ¬ Nat.Prime 262 := by norm_num
  have c263 : count Nat.Prime 263 = 55 := by rw [count_succ, c262, if_neg p262]
  have p263 : Nat.Prime 263 := by norm_num
  have c264 : count Nat.Prime 264 = 56 := by rw [count_succ, c263, if_pos p263]
  have p264 : ¬ Nat.Prime 264 := by norm_num
  have c265 : count Nat.Prime 265 = 56 := by rw [count_succ, c264, if_neg p264]
  have p265 : ¬ Nat.Prime 265 := by norm_num
  have c266 : count Nat.Prime 266 = 56 := by rw [count_succ, c265, if_neg p265]
  have p266 : ¬ Nat.Prime 266 := by norm_num
  have c267 : count Nat.Prime 267 = 56 := by rw [count_succ, c266, if_neg p266]
  have p267 : ¬ Nat.Prime 267 := by norm_num
  have c268 : count Nat.Prime 268 = 56 := by rw [count_succ, c267, if_neg p267]
  have p268 : ¬ Nat.Prime 268 := by norm_num
  have c269 : count Nat.Prime 269 = 56 := by rw [count_succ, c268, if_neg p268]
  have p269 : Nat.Prime 269 := by norm_num
  have c270 : count Nat.Prime 270 = 57 := by rw [count_succ, c269, if_pos p269]
  have p270 : ¬ Nat.Prime 270 := by norm_num
  have c271 : count Nat.Prime 271 = 57 := by rw [count_succ, c270, if_neg p270]
  have p271 : Nat.Prime 271 := by norm_num
  have c272 : count Nat.Prime 272 = 58 := by rw [count_succ, c271, if_pos p271]
  have p272 : ¬ Nat.Prime 272 := by norm_num
  have c273 : count Nat.Prime 273 = 58 := by rw [count_succ, c272, if_neg p272]
  have p273 : ¬ Nat.Prime 273 := by norm_num
  have c274 : count Nat.Prime 274 = 58 := by rw [count_succ, c273, if_neg p273]
  have p274 : ¬ Nat.Prime 274 := by norm_num
  have c275 : count Nat.Prime 275 = 58 := by rw [count_succ, c274, if_neg p274]
  have p275 : ¬ Nat.Prime 275 := by norm_num
  have c276 : count Nat.Prime 276 = 58 := by rw [count_succ, c275, if_neg p275]
  have p276 : ¬ Nat.Prime 276 := by norm_num
  have c277 : count Nat.Prime 277 = 58 := by rw [count_succ, c276, if_neg p276]
  have p277 : Nat.Prime 277 := by norm_num
  have c278 : count Nat.Prime 278 = 59 := by rw [count_succ, c277, if_pos p277]
  have p278 : ¬ Nat.Prime 278 := by norm_num
  have c279 : count Nat.Prime 279 = 59 := by rw [count_succ, c278, if_neg p278]
  have p279 : ¬ Nat.Prime 279 := by norm_num
  have c280 : count Nat.Prime 280 = 59 := by rw [count_succ, c279, if_neg p279]
  have p280 : ¬ Nat.Prime 280 := by norm_num
  have c281 : count Nat.Prime 281 = 59 := by rw [count_succ, c280, if_neg p280]
  have p281 : Nat.Prime 281 := by norm_num
  have c282 : count Nat.Prime 282 = 60 := by rw [count_succ, c281, if_pos p281]
  have p282 : ¬ Nat.Prime 282 := by norm_num
  have c283 : count Nat.Prime 283 = 60 := by rw [count_succ, c282, if_neg p282]
  have p283 : Nat.Prime 283 := by norm_num
  have c284 : count Nat.Prime 284 = 61 := by rw [count_succ, c283, if_pos p283]
  have p284 : ¬ Nat.Prime 284 := by norm_num
  have c285 : count Nat.Prime 285 = 61 := by rw [count_succ, c284, if_neg p284]
  have p285 : ¬ Nat.Prime 285 := by norm_num
  have c286 : count Nat.Prime 286 = 61 := by rw [count_succ, c285, if_neg p285]
  have p286 : ¬ Nat.Prime 286 := by norm_num
  have c287 : count Nat.Prime 287 = 61 := by rw [count_succ, c286, if_neg p286]
  have p287 : ¬ Nat.Prime 287 := by norm_num
  have c288 : count Nat.Prime 288 = 61 := by rw [count_succ, c287, if_neg p287]
  have p288 : ¬ Nat.Prime 288 := by norm_num
  have c289 : count Nat.Prime 289 = 61 := by rw [count_succ, c288, if_neg p288]
  have p289 : ¬ Nat.Prime 289 := by norm_num
  have c290 : count Nat.Prime 290 = 61 := by rw [count_succ, c289, if_neg p289]
  have p290 : ¬ Nat.Prime 290 := by norm_num
  have c291 : count Nat.Prime 291 = 61 := by rw [count_succ, c290, if_neg p290]
  have p291 : ¬ Nat.Prime 291 := by norm_num
  have c292 : count Nat.Prime 292 = 61 := by rw [count_succ, c291, if_neg p291]
  have p292 : ¬ Nat.Prime 292 := by norm_num
  have c293 : count Nat.Prime 293 = 61 := by rw [count_succ, c292, if_neg p292]
  have p293 : Nat.Prime 293 := by norm_num
  have c294 : count Nat.Prime 294 = 62 := by rw [count_succ, c293, if_pos p293]
  have p294 : ¬ Nat.Prime 294 := by norm_num
  have c295 : count Nat.Prime 295 = 62 := by rw [count_succ, c294, if_neg p294]
  have p295 : ¬ Nat.Prime 295 := by norm_num
  have c296 : count Nat.Prime 296 = 62 := by rw [count_succ, c295, if_neg p295]
  have p296 : ¬ Nat.Prime 296 := by norm_num
  have c297 : count Nat.Prime 297 = 62 := by rw [count_succ, c296, if_neg p296]
  have p297 : ¬ Nat.Prime 297 := by norm_num
  have c298 : count Nat.Prime 298 = 62 := by rw [count_succ, c297, if_neg p297]
  have p298 : ¬ Nat.Prime 298 := by norm_num
  have c299 : count Nat.Prime 299 = 62 := by rw [count_succ, c298, if_neg p298]
  have p299 : ¬ Nat.Prime 299 := by norm_num
  have c300 : count Nat.Prime 300 = 62 := by rw [count_succ, c299, if_neg p299]
  have p300 : ¬ Nat.Prime 300 := by norm_num
  have c301 : count Nat.Prime 301 = 62 := by rw [count_succ, c300, if_neg p300]
  have p301 : ¬ Nat.Prime 301 := by norm_num
  have c302 : count Nat.Prime 302 = 62 := by rw [count_succ, c301, if_neg p301]
  have p302 : ¬ Nat.Prime 302 := by norm_num
  have c303 : count Nat.Prime 303 = 62 := by rw [count_succ, c302, if_neg p302]
  have p303 : ¬ Nat.Prime 303 := by norm_num
  have c304 : count Nat.Prime 304 = 62 := by rw [count_succ, c303, if_neg p303]
  have p304 : ¬ Nat.Prime 304 := by norm_num
  have c305 : count Nat.Prime 305 = 62 := by rw [count_succ, c304, if_neg p304]
  have p305 : ¬ Nat.Prime 305 := by norm_num
  have c306 : count Nat.Prime 306 = 62 := by rw [count_succ, c305, if_neg p305]
  have p306 : ¬ Nat.Prime 306 := by norm_num
  have c307 : count Nat.Prime 307 = 62 := by rw [count_succ, c306, if_neg p306]
  have p307 : Nat.Prime 307 := by norm_num
  have c308 : count Nat.Prime 308 = 63 := by rw [count_succ, c307, if_pos p307]
  have p308 : ¬ Nat.Prime 308 := by norm_num
  have c309 : count Nat.Prime 309 = 63 := by rw [count_succ, c308, if_neg p308]
  have p309 : ¬ Nat.Prime 309 := by norm_num
  have c310 : count Nat.Prime 310 = 63 := by rw [count_succ, c309, if_neg p309]
  have p310 : ¬ Nat.Prime 310 := by norm_num
  have c311 : count Nat.Prime 311 = 63 := by rw [count_succ, c310, if_neg p310]
  have p311 : Nat.Prime 311 := by norm_num
  have c312 : count Nat.Prime 312 = 64 := by rw [count_succ, c311, if_pos p311]
  have p312 : ¬ Nat.Prime 312 := by norm_num
  have c313 : count Nat.Prime 313 = 64 := by rw [count_succ, c312, if_neg p312]
  have p313 : Nat.Prime 313 := by norm_num
  have c314 : count Nat.Prime 314 = 65 := by rw [count_succ, c313, if_pos p313]
  have p314 : ¬ Nat.Prime 314 := by norm_num
  have c315 : count Nat.Prime 315 = 65 := by rw [count_succ, c314, if_neg p314]
  have p315 : ¬ Nat.Prime 315 := by norm_num
  have c316 : count Nat.Prime 316 = 65 := by rw [count_succ, c315, if_neg p315]
  have p316 : ¬ Nat.Prime 316 := by norm_num
  have c317 : count Nat.Prime 317 = 65 := by rw [count_succ, c316, if_neg p316]
  have p317 : Nat.Prime 317 := by norm_num
  have c318 : count Nat.Prime 318 = 66 := by rw [count_succ, c317, if_pos p317]
  have p318 : ¬ Nat.Prime 318 := by norm_num
  have c319 : count Nat.Prime 319 = 66 := by rw [count_succ, c318, if_neg p318]
  have p319 : ¬ Nat.Prime 319 := by norm_num
  have c320 : count Nat.Prime 320 = 66 := by rw [count_succ, c319, if_neg p319]
  have p320 : ¬ Nat.Prime 320 := by norm_num
  have c321 : count Nat.Prime 321 = 66 := by rw [count_succ, c320, if_neg p320]
  have p321 : ¬ Nat.Prime 321 := by norm_num
  have c322 : count Nat.Prime 322 = 66 := by rw [count_succ, c321, if_neg p321]
  have p322 : ¬ Nat.Prime 322 := by norm_num
  have c323 : count Nat.Prime 323 = 66 := by rw [count_succ, c322, if_neg p322]
  have p323 : ¬ Nat.Prime 323 := by norm_num
  have c324 : count Nat.Prime 324 = 66 := by rw [count_succ, c323, if_neg p323]
  have p324 : ¬ Nat.Prime 324 := by norm_num
  have c325 : count Nat.Prime 325 = 66 := by rw [count_succ, c324, if_neg p324]
  have p325 : ¬ Nat.Prime 325 := by norm_num
  have c326 : count Nat.Prime 326 = 66 := by rw [count_succ, c325, if_neg p325]
  have p326 : ¬ Nat.Prime 326 := by norm_num
  have c327 : count Nat.Prime 327 = 66 := by rw [count_succ, c326, if_neg p326]
  have p327 : ¬ Nat.Prime 327 := by norm_num
  have c328 : count Nat.Prime 328 = 66 := by rw [count_succ, c327, if_neg p327]
  have p328 : ¬ Nat.Prime 328 := by norm_num
  have c329 : count Nat.Prime 329 = 66 := by rw [count_succ, c328, if_neg p328]
  have p329 : ¬ Nat.Prime 329 := by norm_num
  have c330 : count Nat.Prime 330 = 66 := by rw [count_succ, c329, if_neg p329]
  have p330 : ¬ Nat.Prime 330 := by norm_num
  have c331 : count Nat.Prime 331 = 66 := by rw [count_succ, c330, if_neg p330]
  have p331 : Nat.Prime 331 := by norm_num
  have c332 : count Nat.Prime 332 = 67 := by rw [count_succ, c331, if_pos p331]
  have p332 : ¬ Nat.Prime 332 := by norm_num
  have c333 : count Nat.Prime 333 = 67 := by rw [count_succ, c332, if_neg p332]
  have p333 : ¬ Nat.Prime 333 := by norm_num
  have c334 : count Nat.Prime 334 = 67 := by rw [count_succ, c333, if_neg p333]
  have p334 : ¬ Nat.Prime 334 := by norm_num
  have c335 : count Nat.Prime 335 = 67 := by rw [count_succ, c334, if_neg p334]
  have p335 : ¬ Nat.Prime 335 := by norm_num
  have c336 : count Nat.Prime 336 = 67 := by rw [count_succ, c335, if_neg p335]
  have p336 : ¬ Nat.Prime 336 := by norm_num
  have c337 : count Nat.Prime 337 = 67 := by rw [count_succ, c336, if_neg p336]
  have p337 : Nat.Prime 337 := by norm_num
  have c338 : count Nat.Prime 338 = 68 := by rw [count_succ, c337, if_pos p337]
  have p338 : ¬ Nat.Prime 338 := by norm_num
  have c339 : count Nat.Prime 339 = 68 := by rw [count_succ, c338, if_neg p338]
  have p339 : ¬ Nat.Prime 339 := by norm_num
  have c340 : count Nat.Prime 340 = 68 := by rw [count_succ, c339, if_neg p339]
  have p340 : ¬ Nat.Prime 340 := by norm_num
  have c341 : count Nat.Prime 341 = 68 := by rw [count_succ, c340, if_neg p340]
  have p341 : ¬ Nat.Prime 341 := by norm_num
  have c342 : count Nat.Prime 342 = 68 := by rw [count_succ, c341, if_neg p341]
  have p342 : ¬ Nat.Prime 342 := by norm_num
  have c343 : count Nat.Prime 343 = 68 := by rw [count_succ, c342, if_neg p342]
  have p343 : ¬ Nat.Prime 343 := by norm_num
  have c344 : count Nat.Prime 344 = 68 := by rw [count_succ, c343, if_neg p343]
  have p344 : ¬ Nat.Prime 344 := by norm_num
  have c345 : count Nat.Prime 345 = 68 := by rw [count_succ, c344, if_neg p344]
  have p345 : ¬ Nat.Prime 345 := by norm_num
  have c346 : count Nat.Prime 346 = 68 := by rw [count_succ, c345, if_neg p345]
  have p346 : ¬ Nat.Prime 346 := by norm_num
  have c347 : count Nat.Prime 347 = 68 := by rw [count_succ, c346, if_neg p346]
  have p347 : Nat.Prime 347 := by norm_num
  have c348 : count Nat.Prime 348 = 69 := by rw [count_succ, c347, if_pos p347]
  have p348 : ¬ Nat.Prime 348 := by norm_num
  have c349 : count Nat.Prime 349 = 69 := by rw [count_succ, c348, if_neg p348]
  have p349 : Nat.Prime 349 := by norm_num
  have c350 : count Nat.Prime 350 = 70 := by rw [count_succ, c349, if_pos p349]
  have p350 : ¬ Nat.Prime 350 := by norm_num
  have c351 : count Nat.Prime 351 = 70 := by rw [count_succ, c350, if_neg p350]
  have p351 : ¬ Nat.Prime 351 := by norm_num
  have c352 : count Nat.Prime 352 = 70 := by rw [count_succ, c351, if_neg p351]
  have p352 : ¬ Nat.Prime 352 := by norm_num
  have c353 : count Nat.Prime 353 = 70 := by rw [count_succ, c352, if_neg p352]
  have p353 : Nat.Prime 353 := by norm_num
  have c354 : count Nat.Prime 354 = 71 := by rw [count_succ, c353, if_pos p353]
  have p354 : ¬ Nat.Prime 354 := by norm_num
  have c355 : count Nat.Prime 355 = 71 := by rw [count_succ, c354, if_neg p354]
  have p355 : ¬ Nat.Prime 355 := by norm_num
  have c356 : count Nat.Prime 356 = 71 := by rw [count_succ, c355, if_neg p355]
  have p356 : ¬ Nat.Prime 356 := by norm_num
  have c357 : count Nat.Prime 357 = 71 := by rw [count_succ, c356, if_neg p356]
  have p357 : ¬ Nat.Prime 357 := by norm_num
  have c358 : count Nat.Prime 358 = 71 := by rw [count_succ, c357, if_neg p357]
  have p358 : ¬ Nat.Prime 358 := by norm_num
  have c359 : count Nat.Prime 359 = 71 := by rw [count_succ, c358, if_neg p358]
  have p359 : Nat.Prime 359 := by norm_num
  have c360 : count Nat.Prime 360 = 72 := by rw [count_succ, c359, if_pos p359]
  have p360 : ¬ Nat.Prime 360 := by norm_num
  have c361 : count Nat.Prime 361 = 72 := by rw [count_succ, c360, if_neg p360]
  have p361 : ¬ Nat.Prime 361 := by norm_num
  have c362 : count Nat.Prime 362 = 72 := by rw [count_succ, c361, if_neg p361]
  have p362 : ¬ Nat.Prime 362 := by norm_num
  have c363 : count Nat.Prime 363 = 72 := by rw [count_succ, c362, if_neg p362]
  have p363 : ¬ Nat.Prime 363 := by norm_num
  have c364 : count Nat.Prime 364 = 72 := by rw [count_succ, c363, if_neg p363]
  have p364 : ¬ Nat.Prime 364 := by norm_num
  have c365 : count Nat.Prime 365 = 72 := by rw [count_succ, c364, if_neg p364]
  have p365 : ¬ Nat.Prime 365 := by norm_num
  have c366 : count Nat.Prime 366 = 72 := by rw [count_succ, c365, if_neg p365]
  have p366 : ¬ Nat.Prime 366 := by norm_num
  have c367 : count Nat.Prime 367 = 72 := by rw [count_succ, c366, if_neg p366]
  have p367 : Nat.Prime 367 := by norm_num
  have c368 : count Nat.Prime 368 = 73 := by rw [count_succ, c367, if_pos p367]
  have p368 : ¬ Nat.Prime 368 := by norm_num
  have c369 : count Nat.Prime 369 = 73 := by rw [count_succ, c368, if_neg p368]
  have p369 : ¬ Nat.Prime 369 := by norm_num
  have c370 : count Nat.Prime 370 = 73 := by rw [count_succ, c369, if_neg p369]
  have p370 : ¬ Nat.Prime 370 := by norm_num
  have c371 : count Nat.Prime 371 = 73 := by rw [count_succ, c370, if_neg p370]
  have p371 : ¬ Nat.Prime 371 := by norm_num
  have c372 : count Nat.Prime 372 = 73 := by rw [count_succ, c371, if_neg p371]
  have p372 : ¬ Nat.Prime 372 := by norm_num
  have c373 : count Nat.Prime 373 = 73 := by rw [count_succ, c372, if_neg p372]
  have p373 : Nat.Prime 373 := by norm_num
  have c374 : count Nat.Prime 374 = 74 := by rw [count_succ, c373, if_pos p373]
  have p374 : ¬ Nat.Prime 374 := by norm_num
  have c375 : count Nat.Prime 375 = 74 := by rw [count_succ, c374, if_neg p374]
  have p375 : ¬ Nat.Prime 375 := by norm_num
  have c376 : count Nat.Prime 376 = 74 := by rw [count_succ, c375, if_neg p375]
  have p376 : ¬ Nat.Prime 376 := by norm_num
  have c377 : count Nat.Prime 377 = 74 := by rw [count_succ, c376, if_neg p376]
  have p377 : ¬ Nat.Prime 377 := by norm_num
  have c378 : count Nat.Prime 378 = 74 := by rw [count_succ, c377, if_neg p377]
  have p378 : ¬ Nat.Prime 378 := by norm_num
  have c379 : count Nat.Prime 379 = 74 := by rw [count_succ, c378, if_neg p378]
  have p379 : Nat.Prime 379 := by norm_num
  have c380 : count Nat.Prime 380 = 75 := by rw [count_succ, c379, if_pos p379]
  have p380 : ¬ Nat.Prime 380 := by norm_num
  have c381 : count Nat.Prime 381 = 75 := by rw [count_succ, c380, if_neg p380]
  have p381 : ¬ Nat.Prime 381 := by norm_num
  have c382 : count Nat.Prime 382 = 75 := by rw [count_succ, c381, if_neg p381]
  have p382 : ¬ Nat.Prime 382 := by norm_num
  have c383 : count Nat.Prime 383 = 75 := by rw [count_succ, c382, if_neg p382]
  have p383 : Nat.Prime 383 := by norm_num
  have c384 : count Nat.Prime 384 = 76 := by rw [count_succ, c383, if_pos p383]
  have p384 : ¬ Nat.Prime 384 := by norm_num
  have c385 : count Nat.Prime 385 = 76 := by rw [count_succ, c384, if_neg p384]
  have p385 : ¬ Nat.Prime 385 := by norm_num
  have c386 : count Nat.Prime 386 = 76 := by rw [count_succ, c385, if_neg p385]
  have p386 : ¬ Nat.Prime 386 := by norm_num
  have c387 : count Nat.Prime 387 = 76 := by rw [count_succ, c386, if_neg p386]
  have p387 : ¬ Nat.Prime 387 := by norm_num
  have c388 : count Nat.Prime 388 = 76 := by rw [count_succ, c387, if_neg p387]
  have p388 : ¬ Nat.Prime 388 := by norm_num
  have c389 : count Nat.Prime 389 = 76 := by rw [count_succ, c388, if_neg p388]
  have p389 : Nat.Prime 389 := by norm_num
  have c390 : count Nat.Prime 390 = 77 := by rw [count_succ, c389, if_pos p389]
  have p390 : ¬ Nat.Prime 390 := by norm_num
  have c391 : count Nat.Prime 391 = 77 := by rw [count_succ, c390, if_neg p390]
  have p391 : ¬ Nat.Prime 391 := by norm_num
  have c392 : count Nat.Prime 392 = 77 := by rw [count_succ, c391, if_neg p391]
  have p392 : ¬ Nat.Prime 392 := by norm_num
  have c393 : count Nat.Prime 393 = 77 := by rw [count_succ, c392, if_neg p392]
  have p393 : ¬ Nat.Prime 393 := by norm_num
  have c394 : count Nat.Prime 394 = 77 := by rw [count_succ, c393, if_neg p393]
  have p394 : ¬ Nat.Prime 394 := by norm_num
  have c395 : count Nat.Prime 395 = 77 := by rw [count_succ, c394, if_neg p394]
  have p395 : ¬ Nat.Prime 395 := by norm_num
  have c396 : count Nat.Prime 396 = 77 := by rw [count_succ, c395, if_neg p395]
  have p396 : ¬ Nat.Prime 396 := by norm_num
  have c397 : count Nat.Prime 397 = 77 := by rw [count_succ, c396, if_neg p396]
  have p397 : Nat.Prime 397 := by norm_num
  have c398 : count Nat.Prime 398 = 78 := by rw [count_succ, c397, if_pos p397]
  have p398 : ¬ Nat.Prime 398 := by norm_num
  have c399 : count Nat.Prime 399 = 78 := by rw [count_succ, c398, if_neg p398]
  have p399 : ¬ Nat.Prime 399 := by norm_num
  have c400 : count Nat.Prime 400 = 78 := by rw [count_succ, c399, if_neg p399]
  have p400 : ¬ Nat.Prime 400 := by norm_num
  have c401 : count Nat.Prime 401 = 78 := by rw [count_succ, c400, if_neg p400]
  have p401 : Nat.Prime 401 := by norm_num
  have c402 : count Nat.Prime 402 = 79 := by rw [count_succ, c401, if_pos p401]
  have p402 : ¬ Nat.Prime 402 := by norm_num
  have c403 : count Nat.Prime 403 = 79 := by rw [count_succ, c402, if_neg p402]
  have p403 : ¬ Nat.Prime 403 := by norm_num
  have c404 : count Nat.Prime 404 = 79 := by rw [count_succ, c403, if_neg p403]
  have p404 : ¬ Nat.Prime 404 := by norm_num
  have c405 : count Nat.Prime 405 = 79 := by rw [count_succ, c404, if_neg p404]
  have p405 : ¬ Nat.Prime 405 := by norm_num
  have c406 : count Nat.Prime 406 = 79 := by rw [count_succ, c405, if_neg p405]
  have p406 : ¬ Nat.Prime 406 := by norm_num
  have c407 : count Nat.Prime 407 = 79 := by rw [count_succ, c406, if_neg p406]
  have p407 : ¬ Nat.Prime 407 := by norm_num
  have c408 : count Nat.Prime 408 = 79 := by rw [count_succ, c407, if_neg p407]
  have p408 : ¬ Nat.Prime 408 := by norm_num
  have c409 : count Nat.Prime 409 = 79 := by rw [count_succ, c408, if_neg p408]
  have p409 : Nat.Prime 409 := by norm_num
  have c410 : count Nat.Prime 410 = 80 := by rw [count_succ, c409, if_pos p409]
  have p410 : ¬ Nat.Prime 410 := by norm_num
  have c411 : count Nat.Prime 411 = 80 := by rw [count_succ, c410, if_neg p410]
  have p411 : ¬ Nat.Prime 411 := by norm_num
  have c412 : count Nat.Prime 412 = 80 := by rw [count_succ, c411, if_neg p411]
  have p412 : ¬ Nat.Prime 412 := by norm_num
  have c413 : count Nat.Prime 413 = 80 := by rw [count_succ, c412, if_neg p412]
  have p413 : ¬ Nat.Prime 413 := by norm_num
  have c414 : count Nat.Prime 414 = 80 := by rw [count_succ, c413, if_neg p413]
  have p414 : ¬ Nat.Prime 414 := by norm_num
  have c415 : count Nat.Prime 415 = 80 := by rw [count_succ, c414, if_neg p414]
  have p415 : ¬ Nat.Prime 415 := by norm_num
  have c416 : count Nat.Prime 416 = 80 := by rw [count_succ, c415, if_neg p415]
  have p416 : ¬ Nat.Prime 416 := by norm_num
  have c417 : count Nat.Prime 417 = 80 := by rw [count_succ, c416, if_neg p416]
  have p417 : ¬ Nat.Prime 417 := by norm_num
  have c418 : count Nat.Prime 418 = 80 := by rw [count_succ, c417, if_neg p417]
  have p418 : ¬ Nat.Prime 418 := by norm_num
  have c419 : count Nat.Prime 419 = 80 := by rw [count_succ, c418, if_neg p418]
  have p419 : Nat.Prime 419 := by norm_num
  have c420 : count Nat.Prime 420 = 81 := by rw [count_succ, c419, if_pos p419]
  have p420 : ¬ Nat.Prime 420 := by norm_num
  have c421 : count Nat.Prime 421 = 81 := by rw [count_succ, c420, if_neg p420]
  have p421 : Nat.Prime 421 := by norm_num
  have c422 : count Nat.Prime 422 = 82 := by rw [count_succ, c421, if_pos p421]
  have p422 : ¬ Nat.Prime 422 := by norm_num
  have c423 : count Nat.Prime 423 = 82 := by rw [count_succ, c422, if_neg p422]
  have p423 : ¬ Nat.Prime 423 := by norm_num
  have c424 : count Nat.Prime 424 = 82 := by rw [count_succ, c423, if_neg p423]
  have p424 : ¬ Nat.Prime 424 := by norm_num
  have c425 : count Nat.Prime 425 = 82 := by rw [count_succ, c424, if_neg p424]
  have p425 : ¬ Nat.Prime 425 := by norm_num
  have c426 : count Nat.Prime 426 = 82 := by rw [count_succ, c425, if_neg p425]
  have p426 : ¬ Nat.Prime 426 := by norm_num
  have c427 : count Nat.Prime 427 = 82 := by rw [count_succ, c426, if_neg p426]
  have p427 : ¬ Nat.Prime 427 := by norm_num
  have c428 : count Nat.Prime 428 = 82 := by rw [count_succ, c427, if_neg p427]
  have p428 : ¬ Nat.Prime 428 := by norm_num
  have c429 : count Nat.Prime 429 = 82 := by rw [count_succ, c428, if_neg p428]
  have p429 : ¬ Nat.Prime 429 := by norm_num
  have c430 : count Nat.Prime 430 = 82 := by rw [count_succ, c429, if_neg p429]
  have p430 : ¬ Nat.Prime 430 := by norm_num
  have c431 : count Nat.Prime 431 = 82 := by rw [count_succ, c430, if_neg p430]
  have p431 : Nat.Prime 431 := by norm_num
  have c432 : count Nat.Prime 432 = 83 := by rw [count_succ, c431, if_pos p431]
  have p432 : ¬ Nat.Prime 432 := by norm_num
  have c433 : count Nat.Prime 433 = 83 := by rw [count_succ, c432, if_neg p432]
  have p433 : Nat.Prime 433 := by norm_num
  have c434 : count Nat.Prime 434 = 84 := by rw [count_succ, c433, if_pos p433]
  have p434 : ¬ Nat.Prime 434 := by norm_num
  have c435 : count Nat.Prime 435 = 84 := by rw [count_succ, c434, if_neg p434]
  have p435 : ¬ Nat.Prime 435 := by norm_num
  have c436 : count Nat.Prime 436 = 84 := by rw [count_succ, c435, if_neg p435]
  have p436 : ¬ Nat.Prime 436 := by norm_num
  have c437 : count Nat.Prime 437 = 84 := by rw [count_succ, c436, if_neg p436]
  have p437 : ¬ Nat.Prime 437 := by norm_num
  have c438 : count Nat.Prime 438 = 84 := by rw [count_succ, c437, if_neg p437]
  have p438 : ¬ Nat.Prime 438 := by norm_num
  have c439 : count Nat.Prime 439 = 84 := by rw [count_succ, c438, if_neg p438]
  have p439 : Nat.Prime 439 := by norm_num
  have c440 : count Nat.Prime 440 = 85 := by rw [count_succ, c439, if_pos p439]
  have p440 : ¬ Nat.Prime 440 := by norm_num
  have c441 : count Nat.Prime 441 = 85 := by rw [count_succ, c440, if_neg p440]
  have p441 : ¬ Nat.Prime 441 := by norm_num
  have c442 : count Nat.Prime 442 = 85 := by rw [count_succ, c441, if_neg p441]
  have p442 : ¬ Nat.Prime 442 := by norm_num
  have c443 : count Nat.Prime 443 = 85 := by rw [count_succ, c442, if_neg p442]
  have p443 : Nat.Prime 443 := by norm_num
  have c444 : count Nat.Prime 444 = 86 := by rw [count_succ, c443, if_pos p443]
  have p444 : ¬ Nat.Prime 444 := by norm_num
  have c445 : count Nat.Prime 445 = 86 := by rw [count_succ, c444, if_neg p444]
  have p445 : ¬ Nat.Prime 445 := by norm_num
  have c446 : count Nat.Prime 446 = 86 := by rw [count_succ, c445, if_neg p445]
  have p446 : ¬ Nat.Prime 446 := by norm_num
  have c447 : count Nat.Prime 447 = 86 := by rw [count_succ, c446, if_neg p446]
  have p447 : ¬ Nat.Prime 447 := by norm_num
  have c448 : count Nat.Prime 448 = 86 := by rw [count_succ, c447, if_neg p447]
  have p448 : ¬ Nat.Prime 448 := by norm_num
  have c449 : count Nat.Prime 449 = 86 := by rw [count_succ, c448, if_neg p448]
  have p449 : Nat.Prime 449 := by norm_num
  have c450 : count Nat.Prime 450 = 87 := by rw [count_succ, c449, if_pos p449]
  have p450 : ¬ Nat.Prime 450 := by norm_num
  have c451 : count Nat.Prime 451 = 87 := by rw [count_succ, c450, if_neg p450]
  have p451 : ¬ Nat.Prime 451 := by norm_num
  have c452 : count Nat.Prime 452 = 87 := by rw [count_succ, c451, if_neg p451]
  have p452 : ¬ Nat.Prime 452 := by norm_num
  have c453 : count Nat.Prime 453 = 87 := by rw [count_succ, c452, if_neg p452]
  have p453 : ¬ Nat.Prime 453 := by norm_num
  have c454 : count Nat.Prime 454 = 87 := by rw [count_succ, c453, if_neg p453]
  have p454 : ¬ Nat.Prime 454 := by norm_num
  have c455 : count Nat.Prime 455 = 87 := by rw [count_succ, c454, if_neg p454]
  have p455 : ¬ Nat.Prime 455 := by norm_num
  have c456 : count Nat.Prime 456 = 87 := by rw [count_succ, c455, if_neg p455]
  have p456 : ¬ Nat.Prime 456 := by norm_num
  have c457 : count Nat.Prime 457 = 87 := by rw [count_succ, c456, if_neg p456]
  have p457 : Nat.Prime 457 := by norm_num
  have c458 : count Nat.Prime 458 = 88 := by rw [count_succ, c457, if_pos p457]
  have p458 : ¬ Nat.Prime 458 := by norm_num
  have c459 : count Nat.Prime 459 = 88 := by rw [count_succ, c458, if_neg p458]
  have p459 : ¬ Nat.Prime 459 := by norm_num
  have c460 : count Nat.Prime 460 = 88 := by rw [count_succ, c459, if_neg p459]
  have p460 : ¬ Nat.Prime 460 := by norm_num
  have c461 : count Nat.Prime 461 = 88 := by rw [count_succ, c460, if_neg p460]
  have p461 : Nat.Prime 461 := by norm_num
  have c462 : count Nat.Prime 462 = 89 := by rw [count_succ, c461, if_pos p461]
  have p462 : ¬ Nat.Prime 462 := by norm_num
  have c463 : count Nat.Prime 463 = 89 := by rw [count_succ, c462, if_neg p462]
  have p463 : Nat.Prime 463 := by norm_num
  have c464 : count Nat.Prime 464 = 90 := by rw [count_succ, c463, if_pos p463]
  have p464 : ¬ Nat.Prime 464 := by norm_num
  have c465 : count Nat.Prime 465 = 90 := by rw [count_succ, c464, if_neg p464]
  have p465 : ¬ Nat.Prime 465 := by norm_num
  have c466 : count Nat.Prime 466 = 90 := by rw [count_succ, c465, if_neg p465]
  have p466 : ¬ Nat.Prime 466 := by norm_num
  have c467 : count Nat.Prime 467 = 90 := by rw [count_succ, c466, if_neg p466]
  have p467 : Nat.Prime 467 := by norm_num
  have c468 : count Nat.Prime 468 = 91 := by rw [count_succ, c467, if_pos p467]
  have p468 : ¬ Nat.Prime 468 := by norm_num
  have c469 : count Nat.Prime 469 = 91 := by rw [count_succ, c468, if_neg p468]
  have p469 : ¬ Nat.Prime 469 := by norm_num
  have c470 : count Nat.Prime 470 = 91 := by rw [count_succ, c469, if_neg p469]
  have p470 : ¬ Nat.Prime 470 := by norm_num
  have c471 : count Nat.Prime 471 = 91 := by rw [count_succ, c470, if_neg p470]
  have p471 : ¬ Nat.Prime 471 := by norm_num
  have c472 : count Nat.Prime 472 = 91 := by rw [count_succ, c471, if_neg p471]
  have p472 : ¬ Nat.Prime 472 := by norm_num
  have c473 : count Nat.Prime 473 = 91 := by rw [count_succ, c472, if_neg p472]
  have p473 : ¬ Nat.Prime 473 := by norm_num
  have c474 : count Nat.Prime 474 = 91 := by rw [count_succ, c473, if_neg p473]
  have p474 : ¬ Nat.Prime 474 := by norm_num
  have c475 : count Nat.Prime 475 = 91 := by rw [count_succ, c474, if_neg p474]
  have p475 : ¬ Nat.Prime 475 := by norm_num
  have c476 : count Nat.Prime 476 = 91 := by rw [count_succ, c475, if_neg p475]
  have p476 : ¬ Nat.Prime 476 := by norm_num
  have c477 : count Nat.Prime 477 = 91 := by rw [count_succ, c476, if_neg p476]
  have p477 : ¬ Nat.Prime 477 := by norm_num
  have c478 : count Nat.Prime 478 = 91 := by rw [count_succ, c477, if_neg p477]
  have p478 : ¬ Nat.Prime 478 := by norm_num
  have c479 : count Nat.Prime 479 = 91 := by rw [count_succ, c478, if_neg p478]
  have p479 : Nat.Prime 479 := by norm_num
  have c480 : count Nat.Prime 480 = 92 := by rw [count_succ, c479, if_pos p479]
  have p480 : ¬ Nat.Prime 480 := by norm_num
  have c481 : count Nat.Prime 481 = 92 := by rw [count_succ, c480, if_neg p480]
  have p481 : ¬ Nat.Prime 481 := by norm_num
  have c482 : count Nat.Prime 482 = 92 := by rw [count_succ, c481, if_neg p481]
  have p482 : ¬ Nat.Prime 482 := by norm_num
  have c483 : count Nat.Prime 483 = 92 := by rw [count_succ, c482, if_neg p482]
  have p483 : ¬ Nat.Prime 483 := by norm_num
  have c484 : count Nat.Prime 484 = 92 := by rw [count_succ, c483, if_neg p483]
  have p484 : ¬ Nat.Prime 484 := by norm_num
  have c485 : count Nat.Prime 485 = 92 := by rw [count_succ, c484, if_neg p484]
  have p485 : ¬ Nat.Prime 485 := by norm_num
  have c486 : count Nat.Prime 486 = 92 := by rw [count_succ, c485, if_neg p485]
  have p486 : ¬ Nat.Prime 486 := by norm_num
  have c487 : count Nat.Prime 487 = 92 := by rw [count_succ, c486, if_neg p486]
  have p487 : Nat.Prime 487 := by norm_num
  have c488 : count Nat.Prime 488 = 93 := by rw [count_succ, c487, if_pos p487]
  have p488 : ¬ Nat.Prime 488 := by norm_num
  have c489 : count Nat.Prime 489 = 93 := by rw [count_succ, c488, if_neg p488]
  have p489 : ¬ Nat.Prime 489 := by norm_num
  have c490 : count Nat.Prime 490 = 93 := by rw [count_succ, c489, if_neg p489]
  have p490 : ¬ Nat.Prime 490 := by norm_num
  have c491 : count Nat.Prime 491 = 93 := by rw [count_succ, c490, if_neg p490]
  have p491 : Nat.Prime 491 := by norm_num
  have c492 : count Nat.Prime 492 = 94 := by rw [count_succ, c491, if_pos p491]
  have p492 : ¬ Nat.Prime 492 := by norm_num
  have c493 : count Nat.Prime 493 = 94 := by rw [count_succ, c492, if_neg p492]
  have p493 : ¬ Nat.Prime 493 := by norm_num
  have c494 : count Nat.Prime 494 = 94 := by rw [count_succ, c493, if_neg p493]
  have p494 : ¬ Nat.Prime 494 := by norm_num
  have c495 : count Nat.Prime 495 = 94 := by rw [count_succ, c494, if_neg p494]
  have p495 : ¬ Nat.Prime 495 := by norm_num
  have c496 : count Nat.Prime 496 = 94 := by rw [count_succ, c495, if_neg p495]
  have p496 : ¬ Nat.Prime 496 := by norm_num
  have c497 : count Nat.Prime 497 = 94 := by rw [count_succ, c496, if_neg p496]
  have p497 : ¬ Nat.Prime 497 := by norm_num
  have c498 : count Nat.Prime 498 = 94 := by rw [count_succ, c497, if_neg p497]
  have p498 : ¬ Nat.Prime 498 := by norm_num
  have c499 : count Nat.Prime 499 = 94 := by rw [count_succ, c498, if_neg p498]
  have p499 : Nat.Prime 499 := by norm_num
  have c500 : count Nat.Prime 500 = 95 := by rw [count_succ, c499, if_pos p499]
  have p500 : ¬ Nat.Prime 500 := by norm_num
  have c501 : count Nat.Prime 501 = 95 := by rw [count_succ, c500, if_neg p500]
  have p501 : ¬ Nat.Prime 501 := by norm_num
  have c502 : count Nat.Prime 502 = 95 := by rw [count_succ, c501, if_neg p501]
  have p502 : ¬ Nat.Prime 502 := by norm_num
  have c503 : count Nat.Prime 503 = 95 := by rw [count_succ, c502, if_neg p502]
  have p503 : Nat.Prime 503 := by norm_num
  have c504 : count Nat.Prime 504 = 96 := by rw [count_succ, c503, if_pos p503]
  have p504 : ¬ Nat.Prime 504 := by norm_num
  have c505 : count Nat.Prime 505 = 96 := by rw [count_succ, c504, if_neg p504]
  have p505 : ¬ Nat.Prime 505 := by norm_num
  have c506 : count Nat.Prime 506 = 96 := by rw [count_succ, c505, if_neg p505]
  have p506 : ¬ Nat.Prime 506 := by norm_num
  have c507 : count Nat.Prime 507 = 96 := by rw [count_succ, c506, if_neg p506]
  have p507 : ¬ Nat.Prime 507 := by norm_num
  have c508 : count Nat.Prime 508 = 96 := by rw [count_succ, c507, if_neg p507]
  have p508 : ¬ Nat.Prime 508 := by norm_num
  have c509 : count Nat.Prime 509 = 96 := by rw [count_succ, c508, if_neg p508]
  have p509 : Nat.Prime 509 := by norm_num
  have c510 : count Nat.Prime 510 = 97 := by rw [count_succ, c509, if_pos p509]
  have p510 : ¬ Nat.Prime 510 := by norm_num
  have c511 : count Nat.Prime 511 = 97 := by rw [count_succ, c510, if_neg p510]
  have p511 : ¬ Nat.Prime 511 := by norm_num
  have c512 : count Nat.Prime 512 = 97 := by rw [count_succ, c511, if_neg p511]
  have p512 : ¬ Nat.Prime 512 := by norm_num
  have c513 : count Nat.Prime 513 = 97 := by rw [count_succ, c512, if_neg p512]
  have p513 : ¬ Nat.Prime 513 := by norm_num
  have c514 : count Nat.Prime 514 = 97 := by rw [count_succ, c513, if_neg p513]
  have p514 : ¬ Nat.Prime 514 := by norm_num
  have c515 : count Nat.Prime 515 = 97 := by rw [count_succ, c514, if_neg p514]
  have p515 : ¬ Nat.Prime 515 := by norm_num
  have c516 : count Nat.Prime 516 = 97 := by rw [count_succ, c515, if_neg p515]
  have p516 : ¬ Nat.Prime 516 := by norm_num
  have c517 : count Nat.Prime 517 = 97 := by rw [count_succ, c516, if_neg p516]
  have p517 : ¬ Nat.Prime 517 := by norm_num
  have c518 : count Nat.Prime 518 = 97 := by rw [count_succ, c517, if_neg p517]
  have p518 : ¬ Nat.Prime 518 := by norm_num
  have c519 : count Nat.Prime 519 = 97 := by rw [count_succ, c518, if_neg p518]
  have p519 : ¬ Nat.Prime 519 := by norm_num
  have c520 : count Nat.Prime 520 = 97 := by rw [count_succ, c519, if_neg p519]
  have p520 : ¬ Nat.Prime 520 := by norm_num
  have c521 : count Nat.Prime 521 = 97 := by rw [count_succ, c520, if_neg p520]
  have p521 : Nat.Prime 521 := by norm_num
  have c522 : count Nat.Prime 522 = 98 := by rw [count_succ, c521, if_pos p521]
  have p522 : ¬ Nat.Prime 522 := by norm_num
  have c523 : count Nat.Prime 523 = 98 := by rw [count_succ, c522, if_neg p522]
  have p523 : Nat.Prime 523 := by norm_num
  have c524 : count Nat.Prime 524 = 99 := by rw [count_succ, c523, if_pos p523]
  have p524 : ¬ Nat.Prime 524 := by norm_num
  have c525 : count Nat.Prime 525 = 99 := by rw [count_succ, c524, if_neg p524]
  have p525 : ¬ Nat.Prime 525 := by norm_num
  have c526 : count Nat.Prime 526 = 99 := by rw [count_succ, c525, if_neg p525]
  have p526 : ¬ Nat.Prime 526 := by norm_num
  have c527 : count Nat.Prime 527 = 99 := by rw [count_succ, c526, if_neg p526]
  have p527 : ¬ Nat.Prime 527 := by norm_num
  have c528 : count Nat.Prime 528 = 99 := by rw [count_succ, c527, if_neg p527]
  have p528 : ¬ Nat.Prime 528 := by norm_num
  have c529 : count Nat.Prime 529 = 99 := by rw [count_succ, c528, if_neg p528]
  have p529 : ¬ Nat.Prime 529 := by norm_num
  have c530 : count Nat.Prime 530 = 99 := by rw [count_succ, c529, if_neg p529]
  have p530 : ¬ Nat.Prime 530 := by norm_num
  have c531 : count Nat.Prime 531 = 99 := by rw [count_succ, c530, if_neg p530]
  have p531 : ¬ Nat.Prime 531 := by norm_num
  have c532 : count Nat.Prime 532 = 99 := by rw [count_succ, c531, if_neg p531]
  have p532 : ¬ Nat.Prime 532 := by norm_num
  have c533 : count Nat.Prime 533 = 99 := by rw [count_succ, c532, if_neg p532]
  have p533 : ¬ Nat.Prime 533 := by norm_num
  have c534 : count Nat.Prime 534 = 99 := by rw [count_succ, c533, if_neg p533]
  have p534 : ¬ Nat.Prime 534 := by norm_num
  have c535 : count Nat.Prime 535 = 99 := by rw [count_succ, c534, if_neg p534]
  have p535 : ¬ Nat.Prime 535 := by norm_num
  have c536 : count Nat.Prime 536 = 99 := by rw [count_succ, c535, if_neg p535]
  have p536 : ¬ Nat.Prime 536 := by norm_num
  have c537 : count Nat.Prime 537 = 99 := by rw [count_succ, c536, if_neg p536]
  have p537 : ¬ Nat.Prime 537 := by norm_num
  have c538 : count Nat.Prime 538 = 99 := by rw [count_succ, c537, if_neg p537]
  have p538 : ¬ Nat.Prime 538 := by norm_num
  have c539 : count Nat.Prime 539 = 99 := by rw [count_succ, c538, if_neg p538]
  have p539 : ¬ Nat.Prime 539 := by norm_num
  have c540 : count Nat.Prime 540 = 99 := by rw [count_succ, c539, if_neg p539]
  have p540 : ¬ Nat.Prime 540 := by norm_num
  have c541 : count Nat.Prime 541 = 99 := by rw [count_succ, c540, if_neg p540]
  have p541 : Nat.Prime 541 := by norm_num
  have c542 : count Nat.Prime 542 = 100 := by rw [count_succ, c541, if_pos p541]
  have p542 : ¬ Nat.Prime 542 := by norm_num
  have c543 : count Nat.Prime 543 = 100 := by rw [count_succ, c542, if_neg p542]
  have p543 : ¬ Nat.Prime 543 := by norm_num
  have c544 : count Nat.Prime 544 = 100 := by rw [count_succ, c543, if_neg p543]
  have p544 : ¬ Nat.Prime 544 := by norm_num
  have c545 : count Nat.Prime 545 = 100 := by rw [count_succ, c544, if_neg p544]
  have p545 : ¬ Nat.Prime 545 := by norm_num
  have c546 : count Nat.Prime 546 = 100 := by rw [count_succ, c545, if_neg p545]
  have p546 : ¬ Nat.Prime 546 := by norm_num
  have c547 : count Nat.Prime 547 = 100 := by rw [count_succ, c546, if_neg p546]
  have p547 : Nat.Prime 547 := by norm_num
  have c548 : count Nat.Prime 548 = 101 := by rw [count_succ, c547, if_pos p547]
  have p548 : ¬ Nat.Prime 548 := by norm_num
  have c549 : count Nat.Prime 549 = 101 := by rw [count_succ, c548, if_neg p548]
  have p549 : ¬ Nat.Prime 549 := by norm_num
  have c550 : count Nat.Prime 550 = 101 := by rw [count_succ, c549, if_neg p549]
  have p550 : ¬ Nat.Prime 550 := by norm_num
  have c551 : count Nat.Prime 551 = 101 := by rw [count_succ, c550, if_neg p550]
  have p551 : ¬ Nat.Prime 551 := by norm_num
  have c552 : count Nat.Prime 552 = 101 := by rw [count_succ, c551, if_neg p551]
  have p552 : ¬ Nat.Prime 552 := by norm_num
  have c553 : count Nat.Prime 553 = 101 := by rw [count_succ, c552, if_neg p552]
  have p553 : ¬ Nat.Prime 553 := by norm_num
  have c554 : count Nat.Prime 554 = 101 := by rw [count_succ, c553, if_neg p553]
  have p554 : ¬ Nat.Prime 554 := by norm_num
  have c555 : count Nat.Prime 555 = 101 := by rw [count_succ, c554, if_neg p554]
  have p555 : ¬ Nat.Prime 555 := by norm_num
  have c556 : count Nat.Prime 556 = 101 := by rw [count_succ, c555, if_neg p555]
  have p556 : ¬ Nat.Prime 556 := by norm_num
  have c557 : count Nat.Prime 557 = 101 := by rw [count_succ, c556, if_neg p556]
  have p557 : Nat.Prime 557 := by norm_num
  have c558 : count Nat.Prime 558 = 102 := by rw [count_succ, c557, if_pos p557]
  have p558 : ¬ Nat.Prime 558 := by norm_num
  have c559 : count Nat.Prime 559 = 102 := by rw [count_succ, c558, if_neg p558]
  have p559 : ¬ Nat.Prime 559 := by norm_num
  have c560 : count Nat.Prime 560 = 102 := by rw [count_succ, c559, if_neg p559]
  have p560 : ¬ Nat.Prime 560 := by norm_num
  have c561 : count Nat.Prime 561 = 102 := by rw [count_succ, c560, if_neg p560]
  have p561 : ¬ Nat.Prime 561 := by norm_num
  have c562 : count Nat.Prime 562 = 102 := by rw [count_succ, c561, if_neg p561]
  have p562 : ¬ Nat.Prime 562 := by norm_num
  have c563 : count Nat.Prime 563 = 102 := by rw [count_succ, c562, if_neg p562]
  have p563 : Nat.Prime 563 := by norm_num
  have c564 : count Nat.Prime 564 = 103 := by rw [count_succ, c563, if_pos p563]
  have p564 : ¬ Nat.Prime 564 := by norm_num
  have c565 : count Nat.Prime 565 = 103 := by rw [count_succ, c564, if_neg p564]
  have p565 : ¬ Nat.Prime 565 := by norm_num
  have c566 : count Nat.Prime 566 = 103 := by rw [count_succ, c565, if_neg p565]
  have p566 : ¬ Nat.Prime 566 := by norm_num
  have c567 : count Nat.Prime 567 = 103 := by rw [count_succ, c566, if_neg p566]
  have p567 : ¬ Nat.Prime 567 := by norm_num
  have c568 : count Nat.Prime 568 = 103 := by rw [count_succ, c567, if_neg p567]
  have p568 : ¬ Nat.Prime 568 := by norm_num
  have c569 : count Nat.Prime 569 = 103 := by rw [count_succ, c568, if_neg p568]
  have p569 : Nat.Prime 569 := by norm_num
  have c570 : count Nat.Prime 570 = 104 := by rw [count_succ, c569, if_pos p569]
  have p570 : ¬ Nat.Prime 570 := by norm_num
  have c571 : count Nat.Prime 571 = 104 := by rw [count_succ, c570, if_neg p570]
  have p571 : Nat.Prime 571 := by norm_num
  have c572 : count Nat.Prime 572 = 105 := by rw [count_succ, c571, if_pos p571]
  have p572 : ¬ Nat.Prime 572 := by norm_num
  have c573 : count Nat.Prime 573 = 105 := by rw [count_succ, c572, if_neg p572]
  have p573 : ¬ Nat.Prime 573 := by norm_num
  have c574 : count Nat.Prime 574 = 105 := by rw [count_succ, c573, if_neg p573]
  have p574 : ¬ Nat.Prime 574 := by norm_num
  have c575 : count Nat.Prime 575 = 105 := by rw [count_succ, c574, if_neg p574]
  have p575 : ¬ Nat.Prime 575 := by norm_num
  have c576 : count Nat.Prime 576 = 105 := by rw [count_succ, c575, if_neg p575]
  have p576 : ¬ Nat.Prime 576 := by norm_num
  have c577 : count Nat.Prime 577 = 105 := by rw [count_succ, c576, if_neg p576]
  have p577 : Nat.Prime 577 := by norm_num
  have c578 : count Nat.Prime 578 = 106 := by rw [count_succ, c577, if_pos p577]
  have p578 : ¬ Nat.Prime 578 := by norm_num
  have c579 : count Nat.Prime 579 = 106 := by rw [count_succ, c578, if_neg p578]
  have p579 : ¬ Nat.Prime 579 := by norm_num
  have c580 : count Nat.Prime 580 = 106 := by rw [count_succ, c579, if_neg p579]
  have p580 : ¬ Nat.Prime 580 := by norm_num
  have c581 : count Nat.Prime 581 = 106 := by rw [count_succ, c580, if_neg p580]
  have p581 : ¬ Nat.Prime 581 := by norm_num
  have c582 : count Nat.Prime 582 = 106 := by rw [count_succ, c581, if_neg p581]
  have p582 : ¬ Nat.Prime 582 := by norm_num
  have c583 : count Nat.Prime 583 = 106 := by rw [count_succ, c582, if_neg p582]
  have p583 : ¬ Nat.Prime 583 := by norm_num
  have c584 : count Nat.Prime 584 = 106 := by rw [count_succ, c583, if_neg p583]
  have p584 : ¬ Nat.Prime 584 := by norm_num
  have c585 : count Nat.Prime 585 = 106 := by rw [count_succ, c584, if_neg p584]
  have p585 : ¬ Nat.Prime 585 := by norm_num
  have c586 : count Nat.Prime 586 = 106 := by rw [count_succ, c585, if_neg p585]
  have p586 : ¬ Nat.Prime 586 := by norm_num
  have c587 : count Nat.Prime 587 = 106 := by rw [count_succ, c586, if_neg p586]
  have p587 : Nat.Prime 587 := by norm_num
  have c588 : count Nat.Prime 588 = 107 := by rw [count_succ, c587, if_pos p587]
  have p588 : ¬ Nat.Prime 588 := by norm_num
  have c589 : count Nat.Prime 589 = 107 := by rw [count_succ, c588, if_neg p588]
  have p589 : ¬ Nat.Prime 589 := by norm_num
  have c590 : count Nat.Prime 590 = 107 := by rw [count_succ, c589, if_neg p589]
  have p590 : ¬ Nat.Prime 590 := by norm_num
  have c591 : count Nat.Prime 591 = 107 := by rw [count_succ, c590, if_neg p590]
  have p591 : ¬ Nat.Prime 591 := by norm_num
  have c592 : count Nat.Prime 592 = 107 := by rw [count_succ, c591, if_neg p591]
  have p592 : ¬ Nat.Prime 592 := by norm_num
  have c593 : count Nat.Prime 593 = 107 := by rw [count_succ, c592, if_neg p592]
  have p593 : Nat.Prime 593 := by norm_num
  have c594 : count Nat.Prime 594 = 108 := by rw [count_succ, c593, if_pos p593]
  have p594 : ¬ Nat.Prime 594 := by norm_num
  have c595 : count Nat.Prime 595 = 108 := by rw [count_succ, c594, if_neg p594]
  have p595 : ¬ Nat.Prime 595 := by norm_num
  have c596 : count Nat.Prime 596 = 108 := by rw [count_succ, c595, if_neg p595]
  have p596 : ¬ Nat.Prime 596 := by norm_num
  have c597 : count Nat.Prime 597 = 108 := by rw [count_succ, c596, if_neg p596]
  have p597 : ¬ Nat.Prime 597 := by norm_num
  have c598 : count Nat.Prime 598 = 108 := by rw [count_succ, c597, if_neg p597]
  have p598 : ¬ Nat.Prime 598 := by norm_num
  have c599 : count Nat.Prime 599 = 108 := by rw [count_succ, c598, if_neg p598]
  have p599 : Nat.Prime 599 := by norm_num
  have c600 : count Nat.Prime 600 = 109 := by rw [count_succ, c599, if_pos p599]
  have p600 : ¬ Nat.Prime 600 := by norm_num
  have c601 : count Nat.Prime 601 = 109 := by rw [count_succ, c600, if_neg p600]
  have p601 : Nat.Prime 601 := by norm_num
  have c602 : count Nat.Prime 602 = 110 := by rw [count_succ, c601, if_pos p601]
  have p602 : ¬ Nat.Prime 602 := by norm_num
  have c603 : count Nat.Prime 603 = 110 := by rw [count_succ, c602, if_neg p602]
  have p603 : ¬ Nat.Prime 603 := by norm_num
  have c604 : count Nat.Prime 604 = 110 := by rw [count_succ, c603, if_neg p603]
  have p604 : ¬ Nat.Prime 604 := by norm_num
  have c605 : count Nat.Prime 605 = 110 := by rw [count_succ, c604, if_neg p604]
  have p605 : ¬ Nat.Prime 605 := by norm_num
  have c606 : count Nat.Prime 606 = 110 := by rw [count_succ, c605, if_neg p605]
  have p606 : ¬ Nat.Prime 606 := by norm_num
  have c607 : count Nat.Prime 607 = 110 := by rw [count_succ, c606, if_neg p606]
  have p607 : Nat.Prime 607 := by norm_num
  have c608 : count Nat.Prime 608 = 111 := by rw [count_succ, c607, if_pos p607]
  have p608 : ¬ Nat.Prime 608 := by norm_num
  have c609 : count Nat.Prime 609 = 111 := by rw [count_succ, c608, if_neg p608]
  have p609 : ¬ Nat.Prime 609 := by norm_num
  have c610 : count Nat.Prime 610 = 111 := by rw [count_succ, c609, if_neg p609]
  have p610 : ¬ Nat.Prime 610 := by norm_num
  have c611 : count Nat.Prime 611 = 111 := by rw [count_succ, c610, if_neg p610]
  have p611 : ¬ Nat.Prime 611 := by norm_num
  have c612 : count Nat.Prime 612 = 111 := by rw [count_succ, c611, if_neg p611]
  have p612 : ¬ Nat.Prime 612 := by norm_num
  have c613 : count Nat.Prime 613 = 111 := by rw [count_succ, c612, if_neg p612]
  have p613 : Nat.Prime 613 := by norm_num
  have c614 : count Nat.Prime 614 = 112 := by rw [count_succ, c613, if_pos p613]
  have p614 : ¬ Nat.Prime 614 := by norm_num
  have c615 : count Nat.Prime 615 = 112 := by rw [count_succ, c614, if_neg p614]
  have p615 : ¬ Nat.Prime 615 := by norm_num
  have c616 : count Nat.Prime 616 = 112 := by rw [count_succ, c615, if_neg p615]
  have p616 : ¬ Nat.Prime 616 := by norm_num
  have c617 : count Nat.Prime 617 = 112 := by rw [count_succ, c616, if_neg p616]
  have p617 : Nat.Prime 617 := by norm_num
  have c618 : count Nat.Prime 618 = 113 := by rw [count_succ, c617, if_pos p617]
  have p618 : ¬ Nat.Prime 618 := by norm_num
  have c619 : count Nat.Prime 619 = 113 := by rw [count_succ, c618, if_neg p618]
  have p619 : Nat.Prime 619 := by norm_num
  have c620 : count Nat.Prime 620 = 114 := by rw [count_succ, c619, if_pos p619]
  have p620 : ¬ Nat.Prime 620 := by norm_num
  have c621 : count Nat.Prime 621 = 114 := by rw [count_succ, c620, if_neg p620]
  have p621 : ¬ Nat.Prime 621 := by norm_num
  have c622 : count Nat.Prime 622 = 114 := by rw [count_succ, c621, if_neg p621]
  have p622 : ¬ Nat.Prime 622 := by norm_num
  have c623 : count Nat.Prime 623 = 114 := by rw [count_succ, c622, if_neg p622]
  have p623 : ¬ Nat.Prime 623 := by norm_num
  have c624 : count Nat.Prime 624 = 114 := by rw [count_succ, c623, if_neg p623]
  have p624 : ¬ Nat.Prime 624 := by norm_num
  have c625 : count Nat.Prime 625 = 114 := by rw [count_succ, c624, if_neg p624]
  have p625 : ¬ Nat.Prime 625 := by norm_num
  have c626 : count Nat.Prime 626 = 114 := by rw [count_succ, c625, if_neg p625]
  have p626 : ¬ Nat.Prime 626 := by norm_num
  have c627 : count Nat.Prime 627 = 114 := by rw [count_succ, c626, if_neg p626]
  have p627 : ¬ Nat.Prime 627 := by norm_num
  have c628 : count Nat.Prime 628 = 114 := by rw [count_succ, c627, if_neg p627]
  have p628 : ¬ Nat.Prime 628 := by norm_num
  have c629 : count Nat.Prime 629 = 114 := by rw [count_succ, c628, if_neg p628]
  have p629 : ¬ Nat.Prime 629 := by norm_num
  have c630 : count Nat.Prime 630 = 114 := by rw [count_succ, c629, if_neg p629]
  have p630 : ¬ Nat.Prime 630 := by norm_num
  have c631 : count Nat.Prime 631 = 114 := by rw [count_succ, c630, if_neg p630]
  have p631 : Nat.Prime 631 := by norm_num
  have c632 : count Nat.Prime 632 = 115 := by rw [count_succ, c631, if_pos p631]
  have p632 : ¬ Nat.Prime 632 := by norm_num
  have c633 : count Nat.Prime 633 = 115 := by rw [count_succ, c632, if_neg p632]
  have p633 : ¬ Nat.Prime 633 := by norm_num
  have c634 : count Nat.Prime 634 = 115 := by rw [count_succ, c633, if_neg p633]
  have p634 : ¬ Nat.Prime 634 := by norm_num
  have c635 : count Nat.Prime 635 = 115 := by rw [count_succ, c634, if_neg p634]
  have p635 : ¬ Nat.Prime 635 := by norm_num
  have c636 : count Nat.Prime 636 = 115 := by rw [count_succ, c635, if_neg p635]
  have p636 : ¬ Nat.Prime 636 := by norm_num
  have c637 : count Nat.Prime 637 = 115 := by rw [count_succ, c636, if_neg p636]
  have p637 : ¬ Nat.Prime 637 := by norm_num
  have c638 : count Nat.Prime 638 = 115 := by rw [count_succ, c637, if_neg p637]
  have p638 : ¬ Nat.Prime 638 := by norm_num
  have c639 : count Nat.Prime 639 = 115 := by rw [count_succ, c638, if_neg p638]
  have p639 : ¬ Nat.Prime 639 := by norm_num
  have c640 : count Nat.Prime 640 = 115 := by rw [count_succ, c639, if_neg p639]
  have p640 : ¬ Nat.Prime 640 := by norm_num
  have c641 : count Nat.Prime 641 = 115 := by rw [count_succ, c640, if_neg p640]
  have p641 : Nat.Prime 641 := by norm_num
  have c642 : count Nat.Prime 642 = 116 := by rw [count_succ, c641, if_pos p641]
  have p642 : ¬ Nat.Prime 642 := by norm_num
  have c643 : count Nat.Prime 643 = 116 := by rw [count_succ, c642, if_neg p642]
  have p643 : Nat.Prime 643 := by norm_num
  have c644 : count Nat.Prime 644 = 117 := by rw [count_succ, c643, if_pos p643]
  have p644 : ¬ Nat.Prime 644 := by norm_num
  have c645 : count Nat.Prime 645 = 117 := by rw [count_succ, c644, if_neg p644]
  have p645 : ¬ Nat.Prime 645 := by norm_num
  have c646 : count Nat.Prime 646 = 117 := by rw [count_succ, c645, if_neg p645]
  have p646 : ¬ Nat.Prime 646 := by norm_num
  have c647 : count Nat.Prime 647 = 117 := by rw [count_succ, c646, if_neg p646]
  have p647 : Nat.Prime 647 := by norm_num
  have c648 : count Nat.Prime 648 = 118 := by rw [count_succ, c647, if_pos p647]
  have p648 : ¬ Nat.Prime 648 := by norm_num
  have c649 : count Nat.Prime 649 = 118 := by rw [count_succ, c648, if_neg p648]
  have p649 : ¬ Nat.Prime 649 := by norm_num
  have c650 : count Nat.Prime 650 = 118 := by rw [count_succ, c649, if_neg p649]
  have p650 : ¬ Nat.Prime 650 := by norm_num
  have c651 : count Nat.Prime 651 = 118 := by rw [count_succ, c650, if_neg p650]
  have p651 : ¬ Nat.Prime 651 := by norm_num
  have c652 : count Nat.Prime 652 = 118 := by rw [count_succ, c651, if_neg p651]
  have p652 : ¬ Nat.Prime 652 := by norm_num
  have c653 : count Nat.Prime 653 = 118 := by rw [count_succ, c652, if_neg p652]
  have p653 : Nat.Prime 653 := by norm_num
  have c654 : count Nat.Prime 654 = 119 := by rw [count_succ, c653, if_pos p653]
  have p654 : ¬ Nat.Prime 654 := by norm_num
  have c655 : count Nat.Prime 655 = 119 := by rw [count_succ, c654, if_neg p654]
  have p655 : ¬ Nat.Prime 655 := by norm_num
  have c656 : count Nat.Prime 656 = 119 := by rw [count_succ, c655, if_neg p655]
  have p656 : ¬ Nat.Prime 656 := by norm_num
  have c657 : count Nat.Prime 657 = 119 := by rw [count_succ, c656, if_neg p656]
  have p657 : ¬ Nat.Prime 657 := by norm_num
  have c658 : count Nat.Prime 658 = 119 := by rw [count_succ, c657, if_neg p657]
  have p658 : ¬ Nat.Prime 658 := by norm_num
  have c659 : count Nat.Prime 659 = 119 := by rw [count_succ, c658, if_neg p658]
  have p659 : Nat.Prime 659 := by norm_num
  have c660 : count Nat.Prime 660 = 120 := by rw [count_succ, c659, if_pos p659]
  have p660 : ¬ Nat.Prime 660 := by norm_num
  have c661 : count Nat.Prime 661 = 120 := by rw [count_succ, c660, if_neg p660]
  have p661 : Nat.Prime 661 := by norm_num
  have c662 : count Nat.Prime 662 = 121 := by rw [count_succ, c661, if_pos p661]
  have p662 : ¬ Nat.Prime 662 := by norm_num
  have c663 : count Nat.Prime 663 = 121 := by rw [count_succ, c662, if_neg p662]
  have p663 : ¬ Nat.Prime 663 := by norm_num
  have c664 : count Nat.Prime 664 = 121 := by rw [count_succ, c663, if_neg p663]
  have p664 : ¬ Nat.Prime 664 := by norm_num
  have c665 : count Nat.Prime 665 = 121 := by rw [count_succ, c664, if_neg p664]
  have p665 : ¬ Nat.Prime 665 := by norm_num
  have c666 : count Nat.Prime 666 = 121 := by rw [count_succ, c665, if_neg p665]
  have p666 : ¬ Nat.Prime 666 := by norm_num
  have c667 : count Nat.Prime 667 = 121 := by rw [count_succ, c666, if_neg p666]
  have p667 : ¬ Nat.Prime 667 := by norm_num
  have c668 : count Nat.Prime 668 = 121 := by rw [count_succ, c667, if_neg p667]
  have p668 : ¬ Nat.Prime 668 := by norm_num
  have c669 : count Nat.Prime 669 = 121 := by rw [count_succ, c668, if_neg p668]
  have p669 : ¬ Nat.Prime 669 := by norm_num
  have c670 : count Nat.Prime 670 = 121 := by rw [count_succ, c669, if_neg p669]
  have p670 : ¬ Nat.Prime 670 := by norm_num
  have c671 : count Nat.Prime 671 = 121 := by rw [count_succ, c670, if_neg p670]
  have p671 : ¬ Nat.Prime 671 := by norm_num
  have c672 : count Nat.Prime 672 = 121 := by rw [count_succ, c671, if_neg p671]
  have p672 : ¬ Nat.Prime 672 := by norm_num
  have c673 : count Nat.Prime 673 = 121 := by rw [count_succ, c672, if_neg p672]
  have p673 : Nat.Prime 673 := by norm_num
  have c674 : count Nat.Prime 674 = 122 := by rw [count_succ, c673, if_pos p673]
  have p674 : ¬ Nat.Prime 674 := by norm_num
  have c675 : count Nat.Prime 675 = 122 := by rw [count_succ, c674, if_neg p674]
  have p675 : ¬ Nat.Prime 675 := by norm_num
  have c676 : count Nat.Prime 676 = 122 := by rw [count_succ, c675, if_neg p675]
  have p676 : ¬ Nat.Prime 676 := by norm_num
  have c677 : count Nat.Prime 677 = 122 := by rw [count_succ, c676, if_neg p676]
  have p677 : Nat.Prime 677 := by norm_num
  have c678 : count Nat.Prime 678 = 123 := by rw [count_succ, c677, if_pos p677]
  have p678 : ¬ Nat.Prime 678 := by norm_num
  have c679 : count Nat.Prime 679 = 123 := by rw [count_succ, c678, if_neg p678]
  have p679 : ¬ Nat.Prime 679 := by norm_num
  have c680 : count Nat.Prime 680 = 123 := by rw [count_succ, c679, if_neg p679]
  have p680 : ¬ Nat.Prime 680 := by norm_num
  have c681 : count Nat.Prime 681 = 123 := by rw [count_succ, c680, if_neg p680]
  have p681 : ¬ Nat.Prime 681 := by norm_num
  have c682 : count Nat.Prime 682 = 123 := by rw [count_succ, c681, if_neg p681]
  have p682 : ¬ Nat.Prime 682 := by norm_num
  have c683 : count Nat.Prime 683 = 123 := by rw [count_succ, c682, if_neg p682]
  have p683 : Nat.Prime 683 := by norm_num
  have c684 : count Nat.Prime 684 = 124 := by rw [count_succ, c683, if_pos p683]
  have p684 : ¬ Nat.Prime 684 := by norm_num
  have c685 : count Nat.Prime 685 = 124 := by rw [count_succ, c684, if_neg p684]
  have p685 : ¬ Nat.Prime 685 := by norm_num
  have c686 : count Nat.Prime 686 = 124 := by rw [count_succ, c685, if_neg p685]
  have p686 : ¬ Nat.Prime 686 := by norm_num
  have c687 : count Nat.Prime 687 = 124 := by rw [count_succ, c686, if_neg p686]
  have p687 : ¬ Nat.Prime 687 := by norm_num
  have c688 : count Nat.Prime 688 = 124 := by rw [count_succ, c687, if_neg p687]
  have p688 : ¬ Nat.Prime 688 := by norm_num
  have c689 : count Nat.Prime 689 = 124 := by rw [count_succ, c688, if_neg p688]
  have p689 : ¬ Nat.Prime 689 := by norm_num
  have c690 : count Nat.Prime 690 = 124 := by rw [count_succ, c689, if_neg p689]
  have p690 : ¬ Nat.Prime 690 := by norm_num
  have c691 : count Nat.Prime 691 = 124 := by rw [count_succ, c690, if_neg p690]
  have p691 : Nat.Prime 691 := by norm_num
  have c692 : count Nat.Prime 692 = 125 := by rw [count_succ, c691, if_pos p691]
  have p692 : ¬ Nat.Prime 692 := by norm_num
  have c693 : count Nat.Prime 693 = 125 := by rw [count_succ, c692, if_neg p692]
  have p693 : ¬ Nat.Prime 693 := by norm_num
  have c694 : count Nat.Prime 694 = 125 := by rw [count_succ, c693, if_neg p693]
  have p694 : ¬ Nat.Prime 694 := by norm_num
  have c695 : count Nat.Prime 695 = 125 := by rw [count_succ, c694, if_neg p694]
  have p695 : ¬ Nat.Prime 695 := by norm_num
  have c696 : count Nat.Prime 696 = 125 := by rw [count_succ, c695, if_neg p695]
  have p696 : ¬ Nat.Prime 696 := by norm_num
  have c697 : count Nat.Prime 697 = 125 := by rw [count_succ, c696, if_neg p696]
  have p697 : ¬ Nat.Prime 697 := by norm_num
  have c698 : count Nat.Prime 698 = 125 := by rw [count_succ, c697, if_neg p697]
  have p698 : ¬ Nat.Prime 698 := by norm_num
  have c699 : count Nat.Prime 699 = 125 := by rw [count_succ, c698, if_neg p698]
  have p699 : ¬ Nat.Prime 699 := by norm_num
  have c700 : count Nat.Prime 700 = 125 := by rw [count_succ, c699, if_neg p699]
  have p700 : ¬ Nat.Prime 700 := by norm_num
  have c701 : count Nat.Prime 701 = 125 := by rw [count_succ, c700, if_neg p700]
  have p701 : Nat.Prime 701 := by norm_num
  have c702 : count Nat.Prime 702 = 126 := by rw [count_succ, c701, if_pos p701]
  have p702 : ¬ Nat.Prime 702 := by norm_num
  have c703 : count Nat.Prime 703 = 126 := by rw [count_succ, c702, if_neg p702]
  have p703 : ¬ Nat.Prime 703 := by norm_num
  have c704 : count Nat.Prime 704 = 126 := by rw [count_succ, c703, if_neg p703]
  have p704 : ¬ Nat.Prime 704 := by norm_num
  have c705 : count Nat.Prime 705 = 126 := by rw [count_succ, c704, if_neg p704]
  have p705 : ¬ Nat.Prime 705 := by norm_num
  have c706 : count Nat.Prime 706 = 126 := by rw [count_succ, c705, if_neg p705]
  have p706 : ¬ Nat.Prime 706 := by norm_num
  have c707 : count Nat.Prime 707 = 126 := by rw [count_succ, c706, if_neg p706]
  have p707 : ¬ Nat.Prime 707 := by norm_num
  have c708 : count Nat.Prime 708 = 126 := by rw [count_succ, c707, if_neg p707]
  have p708 : ¬ Nat.Prime 708 := by norm_num
  have c709 : count Nat.Prime 709 = 126 := by rw [count_succ, c708, if_neg p708]
  have p709 : Nat.Prime 709 := by norm_num
  have c710 : count Nat.Prime 710 = 127 := by rw [count_succ, c709, if_pos p709]
  have p710 : ¬ Nat.Prime 710 := by norm_num
  have c711 : count Nat.Prime 711 = 127 := by rw [count_succ, c710, if_neg p710]
  have p711 : ¬ Nat.Prime 711 := by norm_num
  have c712 : count Nat.Prime 712 = 127 := by rw [count_succ, c711, if_neg p711]
  have p712 : ¬ Nat.Prime 712 := by norm_num
  have c713 : count Nat.Prime 713 = 127 := by rw [count_succ, c712, if_neg p712]
  have p713 : ¬ Nat.Prime 713 := by norm_num
  have c714 : count Nat.Prime 714 = 127 := by rw [count_succ, c713, if_neg p713]
  have p714 : ¬ Nat.Prime 714 := by norm_num
  have c715 : count Nat.Prime 715 = 127 := by rw [count_succ, c714, if_neg p714]
  have p715 : ¬ Nat.Prime 715 := by norm_num
  have c716 : count Nat.Prime 716 = 127 := by rw [count_succ, c715, if_neg p715]
  have p716 : ¬ Nat.Prime 716 := by norm_num
  have c717 : count Nat.Prime 717 = 127 := by rw [count_succ, c716, if_neg p716]
  have p717 : ¬ Nat.Prime 717 := by norm_num
  have c718 : count Nat.Prime 718 = 127 := by rw [count_succ, c717, if_neg p717]
  have p718 : ¬ Nat.Prime 718 := by norm_num
  have c719 : count Nat.Prime 719 = 127 := by rw [count_succ, c718, if_neg p718]
  have p719 : Nat.Prime 719 := by norm_num
  have c720 : count Nat.Prime 720 = 128 := by rw [count_succ, c719, if_pos p719]
  have p720 : ¬ Nat.Prime 720 := by norm_num
  have c721 : count Nat.Prime 721 = 128 := by rw [count_succ, c720, if_neg p720]
  have p721 : ¬ Nat.Prime 721 := by norm_num
  have c722 : count Nat.Prime 722 = 128 := by rw [count_succ, c721, if_neg p721]
  have p722 : ¬ Nat.Prime 722 := by norm_num
  have c723 : count Nat.Prime 723 = 128 := by rw [count_succ, c722, if_neg p722]
  have p723 : ¬ Nat.Prime 723 := by norm_num
  have c724 : count Nat.Prime 724 = 128 := by rw [count_succ, c723, if_neg p723]
  have p724 : ¬ Nat.Prime 724 := by norm_num
  have c725 : count Nat.Prime 725 = 128 := by rw [count_succ, c724, if_neg p724]
  have p725 : ¬ Nat.Prime 725 := by norm_num
  have c726 : count Nat.Prime 726 = 128 := by rw [count_succ, c725, if_neg p725]
  have p726 : ¬ Nat.Prime 726 := by norm_num
  have c727 : count Nat.Prime 727 = 128 := by rw [count_succ, c726, if_neg p726]
  have p727 : Nat.Prime 727 := by norm_num
  have c728 : count Nat.Prime 728 = 129 := by rw [count_succ, c727, if_pos p727]
  have p728 : ¬ Nat.Prime 728 := by norm_num
  have c729 : count Nat.Prime 729 = 129 := by rw [count_succ, c728, if_neg p728]
  have p729 : ¬ Nat.Prime 729 := by norm_num
  have c730 : count Nat.Prime 730 = 129 := by rw [count_succ, c729, if_neg p729]
  have p730 : ¬ Nat.Prime 730 := by norm_num
  have c731 : count Nat.Prime 731 = 129 := by rw [count_succ, c730, if_neg p730]
  have p731 : ¬ Nat.Prime 731 := by norm_num
  have c732 : count Nat.Prime 732 = 129 := by rw [count_succ, c731, if_neg p731]
  have p732 : ¬ Nat.Prime 732 := by norm_num
  have c733 : count Nat.Prime 733 = 129 := by rw [count_succ, c732, if_neg p732]
  have p733 : Nat.Prime 733 := by norm_num
  have c734 : count Nat.Prime 734 = 130 := by rw [count_succ, c733, if_pos p733]
  have p734 : ¬ Nat.Prime 734 := by norm_num
  have c735 : count Nat.Prime 735 = 130 := by rw [count_succ, c734, if_neg p734]
  have p735 : ¬ Nat.Prime 735 := by norm_num
  have c736 : count Nat.Prime 736 = 130 := by rw [count_succ, c735, if_neg p735]
  have p736 : ¬ Nat.Prime 736 := by norm_num
  have c737 : count Nat.Prime 737 = 130 := by rw [count_succ, c736, if_neg p736]
  have p737 : ¬ Nat.Prime 737 := by norm_num
  have c738 : count Nat.Prime 738 = 130 := by rw [count_succ, c737, if_neg p737]
  have p738 : ¬ Nat.Prime 738 := by norm_num
  have c739 : count Nat.Prime 739 = 130 := by rw [count_succ, c738, if_neg p738]
  have p739 : Nat.Prime 739 := by norm_num
  have c740 : count Nat.Prime 740 = 131 := by rw [count_succ, c739, if_pos p739]
  have p740 : ¬ Nat.Prime 740 := by norm_num
  have c741 : count Nat.Prime 741 = 131 := by rw [count_succ, c740, if_neg p740]
  have p741 : ¬ Nat.Prime 741 := by norm_num
  have c742 : count Nat.Prime 742 = 131 := by rw [count_succ, c741, if_neg p741]
  have p742 : ¬ Nat.Prime 742 := by norm_num
  have c743 : count Nat.Prime 743 = 131 := by rw [count_succ, c742, if_neg p742]
  have p743 : Nat.Prime 743 := by norm_num
  have c744 : count Nat.Prime 744 = 132 := by rw [count_succ, c743, if_pos p743]
  have p744 : ¬ Nat.Prime 744 := by norm_num
  have c745 : count Nat.Prime 745 = 132 := by rw [count_succ, c744, if_neg p744]
  have p745 : ¬ Nat.Prime 745 := by norm_num
  have c746 : count Nat.Prime 746 = 132 := by rw [count_succ, c745, if_neg p745]
  have p746 : ¬ Nat.Prime 746 := by norm_num
  have c747 : count Nat.Prime 747 = 132 := by rw [count_succ, c746, if_neg p746]
  have p747 : ¬ Nat.Prime 747 := by norm_num
  have c748 : count Nat.Prime 748 = 132 := by rw [count_succ, c747, if_neg p747]
  have p748 : ¬ Nat.Prime 748 := by norm_num
  have c749 : count Nat.Prime 749 = 132 := by rw [count_succ, c748, if_neg p748]
  have p749 : ¬ Nat.Prime 749 := by norm_num
  have c750 : count Nat.Prime 750 = 132 := by rw [count_succ, c749, if_neg p749]
  have p750 : ¬ Nat.Prime 750 := by norm_num
  have c751 : count Nat.Prime 751 = 132 := by rw [count_succ, c750, if_neg p750]
  have p751 : Nat.Prime 751 := by norm_num
  have c752 : count Nat.Prime 752 = 133 := by rw [count_succ, c751, if_pos p751]
  have p752 : ¬ Nat.Prime 752 := by norm_num
  have c753 : count Nat.Prime 753 = 133 := by rw [count_succ, c752, if_neg p752]
  have p753 : ¬ Nat.Prime 753 := by norm_num
  have c754 : count Nat.Prime 754 = 133 := by rw [count_succ, c753, if_neg p753]
  have p754 : ¬ Nat.Prime 754 := by norm_num
  have c755 : count Nat.Prime 755 = 133 := by rw [count_succ, c754, if_neg p754]
  have p755 : ¬ Nat.Prime 755 := by norm_num
  have c756 : count Nat.Prime 756 = 133 := by rw [count_succ, c755, if_neg p755]
  have p756 : ¬ Nat.Prime 756 := by norm_num
  have c757 : count Nat.Prime 757 = 133 := by rw [count_succ, c756, if_neg p756]
  have p757 : Nat.Prime 757 := by norm_num
  have c758 : count Nat.Prime 758 = 134 := by rw [count_succ, c757, if_pos p757]
  have p758 : ¬ Nat.Prime 758 := by norm_num
  have c759 : count Nat.Prime 759 = 134 := by rw [count_succ, c758, if_neg p758]
  have p759 : ¬ Nat.Prime 759 := by norm_num
  have c760 : count Nat.Prime 760 = 134 := by rw [count_succ, c759, if_neg p759]
  have p760 : ¬ Nat.Prime 760 := by norm_num
  have c761 : count Nat.Prime 761 = 134 := by rw [count_succ, c760, if_neg p760]
  have p761 : Nat.Prime 761 := by norm_num
  have c762 : count Nat.Prime 762 = 135 := by rw [count_succ, c761, if_pos p761]
  have p762 : ¬ Nat.Prime 762 := by norm_num
  have c763 : count Nat.Prime 763 = 135 := by rw [count_succ, c762, if_neg p762]
  have p763 : ¬ Nat.Prime 763 := by norm_num
  have c764 : count Nat.Prime 764 = 135 := by rw [count_succ, c763, if_neg p763]
  have p764 : ¬ Nat.Prime 764 := by norm_num
  have c765 : count Nat.Prime 765 = 135 := by rw [count_succ, c764, if_neg p764]
  have p765 : ¬ Nat.Prime 765 := by norm_num
  have c766 : count Nat.Prime 766 = 135 := by rw [count_succ, c765, if_neg p765]
  have p766 : ¬ Nat.Prime 766 := by norm_num
  have c767 : count Nat.Prime 767 = 135 := by rw [count_succ, c766, if_neg p766]
  have p767 : ¬ Nat.Prime 767 := by norm_num
  have c768 : count Nat.Prime 768 = 135 := by rw [count_succ, c767, if_neg p767]
  have p768 : ¬ Nat.Prime 768 := by norm_num
  have c769 : count Nat.Prime 769 = 135 := by rw [count_succ, c768, if_neg p768]
  have p769 : Nat.Prime 769 := by norm_num
  have c770 : count Nat.Prime 770 = 136 := by rw [count_succ, c769, if_pos p769]
  have p770 : ¬ Nat.Prime 770 := by norm_num
  have c771 : count Nat.Prime 771 = 136 := by rw [count_succ, c770, if_neg p770]
  have p771 : ¬ Nat.Prime 771 := by norm_num
  have c772 : count Nat.Prime 772 = 136 := by rw [count_succ, c771, if_neg p771]
  have p772 : ¬ Nat.Prime 772 := by norm_num
  have c773 : count Nat.Prime 773 = 136 := by rw [count_succ, c772, if_neg p772]
  have p773 : Nat.Prime 773 := by norm_num
  have c774 : count Nat.Prime 774 = 137 := by rw [count_succ, c773, if_pos p773]
  have p774 : ¬ Nat.Prime 774 := by norm_num
  have c775 : count Nat.Prime 775 = 137 := by rw [count_succ, c774, if_neg p774]
  have p775 : ¬ Nat.Prime 775 := by norm_num
  have c776 : count Nat.Prime 776 = 137 := by rw [count_succ, c775, if_neg p775]
  have p776 : ¬ Nat.Prime 776 := by norm_num
  have c777 : count Nat.Prime 777 = 137 := by rw [count_succ, c776, if_neg p776]
  have p777 : ¬ Nat.Prime 777 := by norm_num
  have c778 : count Nat.Prime 778 = 137 := by rw [count_succ, c777, if_neg p777]
  have p778 : ¬ Nat.Prime 778 := by norm_num
  have c779 : count Nat.Prime 779 = 137 := by rw [count_succ, c778, if_neg p778]
  have p779 : ¬ Nat.Prime 779 := by norm_num
  have c780 : count Nat.Prime 780 = 137 := by rw [count_succ, c779, if_neg p779]
  have p780 : ¬ Nat.Prime 780 := by norm_num
  have c781 : count Nat.Prime 781 = 137 := by rw [count_succ, c780, if_neg p780]
  have p781 : ¬ Nat.Prime 781 := by norm_num
  have c782 : count Nat.Prime 782 = 137 := by rw [count_succ, c781, if_neg p781]
  have p782 : ¬ Nat.Prime 782 := by norm_num
  have c783 : count Nat.Prime 783 = 137 := by rw [count_succ, c782, if_neg p782]
  have p783 : ¬ Nat.Prime 783 := by norm_num
  have c784 : count Nat.Prime 784 = 137 := by rw [count_succ, c783, if_neg p783]
  have p784 : ¬ Nat.Prime 784 := by norm_num
  have c785 : count Nat.Prime 785 = 137 := by rw [count_succ, c784, if_neg p784]
  have p785 : ¬ Nat.Prime 785 := by norm_num
  have c786 : count Nat.Prime 786 = 137 := by rw [count_succ, c785, if_neg p785]
  have p786 : ¬ Nat.Prime 786 := by norm_num
  have c787 : count Nat.Prime 787 = 137 := by rw [count_succ, c786, if_neg p786]
  have p787 : Nat.Prime 787 := by norm_num
  have c788 : count Nat.Prime 788 = 138 := by rw [count_succ, c787, if_pos p787]
  have p788 : ¬ Nat.Prime 788 := by norm_num
  have c789 : count Nat.Prime 789 = 138 := by rw [count_succ, c788, if_neg p788]
  have p789 : ¬ Nat.Prime 789 := by norm_num
  have c790 : count Nat.Prime 790 = 138 := by rw [count_succ, c789, if_neg p789]
  have p790 : ¬ Nat.Prime 790 := by norm_num
  have c791 : count Nat.Prime 791 = 138 := by rw [count_succ, c790, if_neg p790]
  have p791 : ¬ Nat.Prime 791 := by norm_num
  have c792 : count Nat.Prime 792 = 138 := by rw [count_succ, c791, if_neg p791]
  have p792 : ¬ Nat.Prime 792 := by norm_num
  have c793 : count Nat.Prime 793 = 138 := by rw [count_succ, c792, if_neg p792]
  have p793 : ¬ Nat.Prime 793 := by norm_num
  have c794 : count Nat.Prime 794 = 138 := by rw [count_succ, c793, if_neg p793]
  have p794 : ¬ Nat.Prime 794 := by norm_num
  have c795 : count Nat.Prime 795 = 138 := by rw [count_succ, c794, if_neg p794]
  have p795 : ¬ Nat.Prime 795 := by norm_num
  have c796 : count Nat.Prime 796 = 138 := by rw [count_succ, c795, if_neg p795]
  have p796 : ¬ Nat.Prime 796 := by norm_num
  have c797 : count Nat.Prime 797 = 138 := by rw [count_succ, c796, if_neg p796]
  have p797 : Nat.Prime 797 := by norm_num
  have c798 : count Nat.Prime 798 = 139 := by rw [count_succ, c797, if_pos p797]
  have p798 : ¬ Nat.Prime 798 := by norm_num
  have c799 : count Nat.Prime 799 = 139 := by rw [count_succ, c798, if_neg p798]
  have p799 : ¬ Nat.Prime 799 := by norm_num
  have c800 : count Nat.Prime 800 = 139 := by rw [count_succ, c799, if_neg p799]
  have p800 : ¬ Nat.Prime 800 := by norm_num
  have c801 : count Nat.Prime 801 = 139 := by rw [count_succ, c800, if_neg p800]
  have p801 : ¬ Nat.Prime 801 := by norm_num
  have c802 : count Nat.Prime 802 = 139 := by rw [count_succ, c801, if_neg p801]
  have p802 : ¬ Nat.Prime 802 := by norm_num
  have c803 : count Nat.Prime 803 = 139 := by rw [count_succ, c802, if_neg p802]
  have p803 : ¬ Nat.Prime 803 := by norm_num
  have c804 : count Nat.Prime 804 = 139 := by rw [count_succ, c803, if_neg p803]
  have p804 : ¬ Nat.Prime 804 := by norm_num
  have c805 : count Nat.Prime 805 = 139 := by rw [count_succ, c804, if_neg p804]
  have p805 : ¬ Nat.Prime 805 := by norm_num
  have c806 : count Nat.Prime 806 = 139 := by rw [count_succ, c805, if_neg p805]
  have p806 : ¬ Nat.Prime 806 := by norm_num
  have c807 : count Nat.Prime 807 = 139 := by rw [count_succ, c806, if_neg p806]
  have p807 : ¬ Nat.Prime 807 := by norm_num
  have c808 : count Nat.Prime 808 = 139 := by rw [count_succ, c807, if_neg p807]
  have p808 : ¬ Nat.Prime 808 := by norm_num
  have c809 : count Nat.Prime 809 = 139 := by rw [count_succ, c808, if_neg p808]
  have p809 : Nat.Prime 809 := by norm_num
  have c810 : count Nat.Prime 810 = 140 := by rw [count_succ, c809, if_pos p809]
  have p810 : ¬ Nat.Prime 810 := by norm_num
  have c811 : count Nat.Prime 811 = 140 := by rw [count_succ, c810, if_neg p810]
  have p811 : Nat.Prime 811 := by norm_num
  have c812 : count Nat.Prime 812 = 141 := by rw [count_succ, c811, if_pos p811]
  have p812 : ¬ Nat.Prime 812 := by norm_num
  have c813 : count Nat.Prime 813 = 141 := by rw [count_succ, c812, if_neg p812]
  have p813 : ¬ Nat.Prime 813 := by norm_num
  have c814 : count Nat.Prime 814 = 141 := by rw [count_succ, c813, if_neg p813]
  have p814 : ¬ Nat.Prime 814 := by norm_num
  have c815 : count Nat.Prime 815 = 141 := by rw [count_succ, c814, if_neg p814]
  have p815 : ¬ Nat.Prime 815 := by norm_num
  have c816 : count Nat.Prime 816 = 141 := by rw [count_succ, c815, if_neg p815]
  have p816 : ¬ Nat.Prime 816 := by norm_num
  have c817 : count Nat.Prime 817 = 141 := by rw [count_succ, c816, if_neg p816]
  have p817 : ¬ Nat.Prime 817 := by norm_num
  have c818 : count Nat.Prime 818 = 141 := by rw [count_succ, c817, if_neg p817]
  have p818 : ¬ Nat.Prime 818 := by norm_num
  have c819 : count Nat.Prime 819 = 141 := by rw [count_succ, c818, if_neg p818]
  have p819 : ¬ Nat.Prime 819 := by norm_num
  have c820 : count Nat.Prime 820 = 141 := by rw [count_succ, c819, if_neg p819]
  have p820 : ¬ Nat.Prime 820 := by norm_num
  have c821 : count Nat.Prime 821 = 141 := by rw [count_succ, c820, if_neg p820]
  have p821 : Nat.Prime 821 := by norm_num
  have c822 : count Nat.Prime 822 = 142 := by rw [count_succ, c821, if_pos p821]
  have p822 : ¬ Nat.Prime 822 := by norm_num
  have c823 : count Nat.Prime 823 = 142 := by rw [count_succ, c822, if_neg p822]
  have p823 : Nat.Prime 823 := by norm_num
  have c824 : count Nat.Prime 824 = 143 := by rw [count_succ, c823, if_pos p823]
  have p824 : ¬ Nat.Prime 824 := by norm_num
  have c825 : count Nat.Prime 825 = 143 := by rw [count_succ, c824, if_neg p824]
  have p825 : ¬ Nat.Prime 825 := by norm_num
  have c826 : count Nat.Prime 826 = 143 := by rw [count_succ, c825, if_neg p825]
  have p826 : ¬ Nat.Prime 826 := by norm_num
  have c827 : count Nat.Prime 827 = 143 := by rw [count_succ, c826, if_neg p826]
  have p827 : Nat.Prime 827 := by norm_num
  have c828 : count Nat.Prime 828 = 144 := by rw [count_succ, c827, if_pos p827]
  have p828 : ¬ Nat.Prime 828 := by norm_num
  have c829 : count Nat.Prime 829 = 144 := by rw [count_succ, c828, if_neg p828]
  have p829 : Nat.Prime 829 := by norm_num
  have c830 : count Nat.Prime 830 = 145 := by rw [count_succ, c829, if_pos p829]
  have p830 : ¬ Nat.Prime 830 := by norm_num
  have c831 : count Nat.Prime 831 = 145 := by rw [count_succ, c830, if_neg p830]
  have p831 : ¬ Nat.Prime 831 := by norm_num
  have c832 : count Nat.Prime 832 = 145 := by rw [count_succ, c831, if_neg p831]
  have p832 : ¬ Nat.Prime 832 := by norm_num
  have c833 : count Nat.Prime 833 = 145 := by rw [count_succ, c832, if_neg p832]
  have p833 : ¬ Nat.Prime 833 := by norm_num
  have c834 : count Nat.Prime 834 = 145 := by rw [count_succ, c833, if_neg p833]
  have p834 : ¬ Nat.Prime 834 := by norm_num
  have c835 : count Nat.Prime 835 = 145 := by rw [count_succ, c834, if_neg p834]
  have p835 : ¬ Nat.Prime 835 := by norm_num
  have c836 : count Nat.Prime 836 = 145 := by rw [count_succ, c835, if_neg p835]
  have p836 : ¬ Nat.Prime 836 := by norm_num
  have c837 : count Nat.Prime 837 = 145 := by rw [count_succ, c836, if_neg p836]
  have p837 : ¬ Nat.Prime 837 := by norm_num
  have c838 : count Nat.Prime 838 = 145 := by rw [count_succ, c837, if_neg p837]
  have p838 : ¬ Nat.Prime 838 := by norm_num
  have c839 : count Nat.Prime 839 = 145 := by rw [count_succ, c838, if_neg p838]
  have p839 : Nat.Prime 839 := by norm_num
  have c840 : count Nat.Prime 840 = 146 := by rw [count_succ, c839, if_pos p839]
  have p840 : ¬ Nat.Prime 840 := by norm_num
  have c841 : count Nat.Prime 841 = 146 := by rw [count_succ, c840, if_neg p840]
  have p841 : ¬ Nat.Prime 841 := by norm_num
  have c842 : count Nat.Prime 842 = 146 := by rw [count_succ, c841, if_neg p841]
  have p842 : ¬ Nat.Prime 842 := by norm_num
  have c843 : count Nat.Prime 843 = 146 := by rw [count_succ, c842, if_neg p842]
  have p843 : ¬ Nat.Prime 843 := by norm_num
  have c844 : count Nat.Prime 844 = 146 := by rw [count_succ, c843, if_neg p843]
  have p844 : ¬ Nat.Prime 844 := by norm_num
  have c845 : count Nat.Prime 845 = 146 := by rw [count_succ, c844, if_neg p844]
  have p845 : ¬ Nat.Prime 845 := by norm_num
  have c846 : count Nat.Prime 846 = 146 := by rw [count_succ, c845, if_neg p845]
  have p846 : ¬ Nat.Prime 846 := by norm_num
  have c847 : count Nat.Prime 847 = 146 := by rw [count_succ, c846, if_neg p846]
  have p847 : ¬ Nat.Prime 847 := by norm_num
  have c848 : count Nat.Prime 848 = 146 := by rw [count_succ, c847, if_neg p847]
  have p848 : ¬ Nat.Prime 848 := by norm_num
  have c849 : count Nat.Prime 849 = 146 := by rw [count_succ, c848, if_neg p848]
  have p849 : ¬ Nat.Prime 849 := by norm_num
  have c850 : count Nat.Prime 850 = 146 := by rw [count_succ, c849, if_neg p849]
  have p850 : ¬ Nat.Prime 850 := by norm_num
  have c851 : count Nat.Prime 851 = 146 := by rw [count_succ, c850, if_neg p850]
  have p851 : ¬ Nat.Prime 851 := by norm_num
  have c852 : count Nat.Prime 852 = 146 := by rw [count_succ, c851, if_neg p851]
  have p852 : ¬ Nat.Prime 852 := by norm_num
  have c853 : count Nat.Prime 853 = 146 := by rw [count_succ, c852, if_neg p852]
  have p853 : Nat.Prime 853 := by norm_num
  have c854 : count Nat.Prime 854 = 147 := by rw [count_succ, c853, if_pos p853]
  have p854 : ¬ Nat.Prime 854 := by norm_num
  have c855 : count Nat.Prime 855 = 147 := by rw [count_succ, c854, if_neg p854]
  have p855 : ¬ Nat.Prime 855 := by norm_num
  have c856 : count Nat.Prime 856 = 147 := by rw [count_succ, c855, if_neg p855]
  have p856 : ¬ Nat.Prime 856 := by norm_num
  have c857 : count Nat.Prime 857 = 147 := by rw [count_succ, c856, if_neg p856]
  have p857 : Nat.Prime 857 := by norm_num
  have c858 : count Nat.Prime 858 = 148 := by rw [count_succ, c857, if_pos p857]
  have p858 : ¬ Nat.Prime 858 := by norm_num
  have c859 : count Nat.Prime 859 = 148 := by rw [count_succ, c858, if_neg p858]
  have p859 : Nat.Prime 859 := by norm_num
  have c860 : count Nat.Prime 860 = 149 := by rw [count_succ, c859, if_pos p859]
  have p860 : ¬ Nat.Prime 860 := by norm_num
  have c861 : count Nat.Prime 861 = 149 := by rw [count_succ, c860, if_neg p860]
  have p861 : ¬ Nat.Prime 861 := by norm_num
  have c862 : count Nat.Prime 862 = 149 := by rw [count_succ, c861, if_neg p861]
  have p862 : ¬ Nat.Prime 862 := by norm_num
  have c863 : count Nat.Prime 863 = 149 := by rw [count_succ, c862, if_neg p862]
  have p863 : Nat.Prime 863 := by norm_num
  have c864 : count Nat.Prime 864 = 150 := by rw [count_succ, c863, if_pos p863]
  have p864 : ¬ Nat.Prime 864 := by norm_num
  have c865 : count Nat.Prime 865 = 150 := by rw [count_succ, c864, if_neg p864]
  have p865 : ¬ Nat.Prime 865 := by norm_num
  have c866 : count Nat.Prime 866 = 150 := by rw [count_succ, c865, if_neg p865]
  have p866 : ¬ Nat.Prime 866 := by norm_num
  have c867 : count Nat.Prime 867 = 150 := by rw [count_succ, c866, if_neg p866]
  have p867 : ¬ Nat.Prime 867 := by norm_num
  have c868 : count Nat.Prime 868 = 150 := by rw [count_succ, c867, if_neg p867]
  have p868 : ¬ Nat.Prime 868 := by norm_num
  have c869 : count Nat.Prime 869 = 150 := by rw [count_succ, c868, if_neg p868]
  have p869 : ¬ Nat.Prime 869 := by norm_num
  have c870 : count Nat.Prime 870 = 150 := by rw [count_succ, c869, if_neg p869]
  have p870 : ¬ Nat.Prime 870 := by norm_num
  have c871 : count Nat.Prime 871 = 150 := by rw [count_succ, c870, if_neg p870]
  have p871 : ¬ Nat.Prime 871 := by norm_num
  have c872 : count Nat.Prime 872 = 150 := by rw [count_succ, c871, if_neg p871]
  have p872 : ¬ Nat.Prime 872 := by norm_num
  have c873 : count Nat.Prime 873 = 150 := by rw [count_succ, c872, if_neg p872]
  have p873 : ¬ Nat.Prime 873 := by norm_num
  have c874 : count Nat.Prime 874 = 150 := by rw [count_succ, c873, if_neg p873]
  have p874 : ¬ Nat.Prime 874 := by norm_num
  have c875 : count Nat.Prime 875 = 150 := by rw [count_succ, c874, if_neg p874]
  have p875 : ¬ Nat.Prime 875 := by norm_num
  have c876 : count Nat.Prime 876 = 150 := by rw [count_succ, c875, if_neg p875]
  have p876 : ¬ Nat.Prime 876 := by norm_num
  have c877 : count Nat.Prime 877 = 150 := by rw [count_succ, c876, if_neg p876]
  have p877 : Nat.Prime 877 := by norm_num
  have c878 : count Nat.Prime 878 = 151 := by rw [count_succ, c877, if_pos p877]
  have p878 : ¬ Nat.Prime 878 := by norm_num
  have c879 : count Nat.Prime 879 = 151 := by rw [count_succ, c878, if_neg p878]
  have p879 : ¬ Nat.Prime 879 := by norm_num
  have c880 : count Nat.Prime 880 = 151 := by rw [count_succ, c879, if_neg p879]
  have p880 : ¬ Nat.Prime 880 := by norm_num
  have c881 : count Nat.Prime 881 = 151 := by rw [count_succ, c880, if_neg p880]
  have p881 : Nat.Prime 881 := by norm_num
  have c882 : count Nat.Prime 882 = 152 := by rw [count_succ, c881, if_pos p881]
  have p882 : ¬ Nat.Prime 882 := by norm_num
  have c883 : count Nat.Prime 883 = 152 := by rw [count_succ, c882, if_neg p882]
  have p883 : Nat.Prime 883 := by norm_num
  have c884 : count Nat.Prime 884 = 153 := by rw [count_succ, c883, if_pos p883]
  have p884 : ¬ Nat.Prime 884 := by norm_num
  have c885 : count Nat.Prime 885 = 153 := by rw [count_succ, c884, if_neg p884]
  have p885 : ¬ Nat.Prime 885 := by norm_num
  have c886 : count Nat.Prime 886 = 153 := by rw [count_succ, c885, if_neg p885]
  have p886 : ¬ Nat.Prime 886 := by norm_num
  have c887 : count Nat.Prime 887 = 153 := by rw [count_succ, c886, if_neg p886]
  have p887 : Nat.Prime 887 := by norm_num
  have c888 : count Nat.Prime 888 = 154 := by rw [count_succ, c887, if_pos p887]
  have p888 : ¬ Nat.Prime 888 := by norm_num
  have c889 : count Nat.Prime 889 = 154 := by rw [count_succ, c888, if_neg p888]
  have p889 : ¬ Nat.Prime 889 := by norm_num
  have c890 : count Nat.Prime 890 = 154 := by rw [count_succ, c889, if_neg p889]
  have p890 : ¬ Nat.Prime 890 := by norm_num
  have c891 : count Nat.Prime 891 = 154 := by rw [count_succ, c890, if_neg p890]
  have p891 : ¬ Nat.Prime 891 := by norm_num
  have c892 : count Nat.Prime 892 = 154 := by rw [count_succ, c891, if_neg p891]
  have p892 : ¬ Nat.Prime 892 := by norm_num
  have c893 : count Nat.Prime 893 = 154 := by rw [count_succ, c892, if_neg p892]
  have p893 : ¬ Nat.Prime 893 := by norm_num
  have c894 : count Nat.Prime 894 = 154 := by rw [count_succ, c893, if_neg p893]
  have p894 : ¬ Nat.Prime 894 := by norm_num
  have c895 : count Nat.Prime 895 = 154 := by rw [count_succ, c894, if_neg p894]
  have p895 : ¬ Nat.Prime 895 := by norm_num
  have c896 : count Nat.Prime 896 = 154 := by rw [count_succ, c895, if_neg p895]
  have p896 : ¬ Nat.Prime 896 := by norm_num
  have c897 : count Nat.Prime 897 = 154 := by rw [count_succ, c896, if_neg p896]
  have p897 : ¬ Nat.Prime 897 := by norm_num
  have c898 : count Nat.Prime 898 = 154 := by rw [count_succ, c897, if_neg p897]
  have p898 : ¬ Nat.Prime 898 := by norm_num
  have c899 : count Nat.Prime 899 = 154 := by rw [count_succ, c898, if_neg p898]
  have p899 : ¬ Nat.Prime 899 := by norm_num
  have c900 : count Nat.Prime 900 = 154 := by rw [count_succ, c899, if_neg p899]
  have p900 : ¬ Nat.Prime 900 := by norm_num
  have c901 : count Nat.Prime 901 = 154 := by rw [count_succ, c900, if_neg p900]
  have p901 : ¬ Nat.Prime 901 := by norm_num
  have c902 : count Nat.Prime 902 = 154 := by rw [count_succ, c901, if_neg p901]
  have p902 : ¬ Nat.Prime 902 := by norm_num
  have c903 : count Nat.Prime 903 = 154 := by rw [count_succ, c902, if_neg p902]
  have p903 : ¬ Nat.Prime 903 := by norm_num
  have c904 : count Nat.Prime 904 = 154 := by rw [count_succ, c903, if_neg p903]
  have p904 : ¬ Nat.Prime 904 := by norm_num
  have c905 : count Nat.Prime 905 = 154 := by rw [count_succ, c904, if_neg p904]
  have p905 : ¬ Nat.Prime 905 := by norm_num
  have c906 : count Nat.Prime 906 = 154 := by rw [count_succ, c905, if_neg p905]
  have p906 : ¬ Nat.Prime 906 := by norm_num
  have c907 : count Nat.Prime 907 = 154 := by rw [count_succ, c906, if_neg p906]
  have p907 : Nat.Prime 907 := by norm_num
  have c908 : count Nat.Prime 908 = 155 := by rw [count_succ, c907, if_pos p907]
  have p908 : ¬ Nat.Prime 908 := by norm_num
  have c909 : count Nat.Prime 909 = 155 := by rw [count_succ, c908, if_neg p908]
  have p909 : ¬ Nat.Prime 909 := by norm_num
  have c910 : count Nat.Prime 910 = 155 := by rw [count_succ, c909, if_neg p909]
  have p910 : ¬ Nat.Prime 910 := by norm_num
  have c911 : count Nat.Prime 911 = 155 := by rw [count_succ, c910, if_neg p910]
  have p911 : Nat.Prime 911 := by norm_num
  have c912 : count Nat.Prime 912 = 156 := by rw [count_succ, c911, if_pos p911]
  have p912 : ¬ Nat.Prime 912 := by norm_num
  have c913 : count Nat.Prime 913 = 156 := by rw [count_succ, c912, if_neg p912]
  have p913 : ¬ Nat.Prime 913 := by norm_num
  have c914 : count Nat.Prime 914 = 156 := by rw [count_succ, c913, if_neg p913]
  have p914 : ¬ Nat.Prime 914 := by norm_num
  have c915 : count Nat.Prime 915 = 156 := by rw [count_succ, c914, if_neg p914]
  have p915 : ¬ Nat.Prime 915 := by norm_num
  have c916 : count Nat.Prime 916 = 156 := by rw [count_succ, c915, if_neg p915]
  have p916 : ¬ Nat.Prime 916 := by norm_num
  have c917 : count Nat.Prime 917 = 156 := by rw [count_succ, c916, if_neg p916]
  have p917 : ¬ Nat.Prime 917 := by norm_num
  have c918 : count Nat.Prime 918 = 156 := by rw [count_succ, c917, if_neg p917]
  have p918 : ¬ Nat.Prime 918 := by norm_num
  have c919 : count Nat.Prime 919 = 156 := by rw [count_succ, c918, if_neg p918]
  have p919 : Nat.Prime 919 := by norm_num
  have c920 : count Nat.Prime 920 = 157 := by rw [count_succ, c919, if_pos p919]
  have p920 : ¬ Nat.Prime 920 := by norm_num
  have c921 : count Nat.Prime 921 = 157 := by rw [count_succ, c920, if_neg p920]
  have p921 : ¬ Nat.Prime 921 := by norm_num
  have c922 : count Nat.Prime 922 = 157 := by rw [count_succ, c921, if_neg p921]
  have p922 : ¬ Nat.Prime 922 := by norm_num
  have c923 : count Nat.Prime 923 = 157 := by rw [count_succ, c922, if_neg p922]
  have p923 : ¬ Nat.Prime 923 := by norm_num
  have c924 : count Nat.Prime 924 = 157 := by rw [count_succ, c923, if_neg p923]
  have p924 : ¬ Nat.Prime 924 := by norm_num
  have c925 : count Nat.Prime 925 = 157 := by rw [count_succ, c924, if_neg p924]
  have p925 : ¬ Nat.Prime 925 := by norm_num
  have c926 : count Nat.Prime 926 = 157 := by rw [count_succ, c925, if_neg p925]
  have p926 : ¬ Nat.Prime 926 := by norm_num
  have c927 : count Nat.Prime 927 = 157 := by rw [count_succ, c926, if_neg p926]
  have p927 : ¬ Nat.Prime 927 := by norm_num
  have c928 : count Nat.Prime 928 = 157 := by rw [count_succ, c927, if_neg p927]
  have p928 : ¬ Nat.Prime 928 := by norm_num
  have c929 : count Nat.Prime 929 = 157 := by rw [count_succ, c928, if_neg p928]
  have p929 : Nat.Prime 929 := by norm_num
  have c930 : count Nat.Prime 930 = 158 := by rw [count_succ, c929, if_pos p929]
  have p930 : ¬ Nat.Prime 930 := by norm_num
  have c931 : count Nat.Prime 931 = 158 := by rw [count_succ, c930, if_neg p930]
  have p931 : ¬ Nat.Prime 931 := by norm_num
  have c932 : count Nat.Prime 932 = 158 := by rw [count_succ, c931, if_neg p931]
  have p932 : ¬ Nat.Prime 932 := by norm_num
  have c933 : count Nat.Prime 933 = 158 := by rw [count_succ, c932, if_neg p932]
  have p933 : ¬ Nat.Prime 933 := by norm_num
  have c934 : count Nat.Prime 934 = 158 := by rw [count_succ, c933, if_neg p933]
  have p934 : ¬ Nat.Prime 934 := by norm_num
  have c935 : count Nat.Prime 935 = 158 := by rw [count_succ, c934, if_neg p934]
  have p935 : ¬ Nat.Prime 935 := by norm_num
  have c936 : count Nat.Prime 936 = 158 := by rw [count_succ, c935, if_neg p935]
  have p936 : ¬ Nat.Prime 936 := by norm_num
  have c937 : count Nat.Prime 937 = 158 := by rw [count_succ, c936, if_neg p936]
  have p937 : Nat.Prime 937 := by norm_num
  have c938 : count Nat.Prime 938 = 159 := by rw [count_succ, c937, if_pos p937]
  have p938 : ¬ Nat.Prime 938 := by norm_num
  have c939 : count Nat.Prime 939 = 159 := by rw [count_succ, c938, if_neg p938]
  have p939 : ¬ Nat.Prime 939 := by norm_num
  have c940 : count Nat.Prime 940 = 159 := by rw [count_succ, c939, if_neg p939]
  have p940 : ¬ Nat.Prime 940 := by norm_num
  have c941 : count Nat.Prime 941 = 159 := by rw [count_succ, c940, if_neg p940]
  have p941 : Nat.Prime 941 := by norm_num
  have c942 : count Nat.Prime 942 = 160 := by rw [count_succ, c941, if_pos p941]
  have p942 : ¬ Nat.Prime 942 := by norm_num
  have c943 : count Nat.Prime 943 = 160 := by rw [count_succ, c942, if_neg p942]
  have p943 : ¬ Nat.Prime 943 := by norm_num
  have c944 : count Nat.Prime 944 = 160 := by rw [count_succ, c943, if_neg p943]
  have p944 : ¬ Nat.Prime 944 := by norm_num
  have c945 : count Nat.Prime 945 = 160 := by rw [count_succ, c944, if_neg p944]
  have p945 : ¬ Nat.Prime 945 := by norm_num
  have c946 : count Nat.Prime 946 = 160 := by rw [count_succ, c945, if_neg p945]
  have p946 : ¬ Nat.Prime 946 := by norm_num
  have c947 : count Nat.Prime 947 = 160 := by rw [count_succ, c946, if_neg p946]
  have p947 : Nat.Prime 947 := by norm_num
  have c948 : count Nat.Prime 948 = 161 := by rw [count_succ, c947, if_pos p947]
  have p948 : ¬ Nat.Prime 948 := by norm_num
  have c949 : count Nat.Prime 949 = 161 := by rw [count_succ, c948, if_neg p948]
  have p949 : ¬ Nat.Prime 949 := by norm_num
  have c950 : count Nat.Prime 950 = 161 := by rw [count_succ, c949, if_neg p949]
  have p950 : ¬ Nat.Prime 950 := by norm_num
  have c951 : count Nat.Prime 951 = 161 := by rw [count_succ, c950, if_neg p950]
  have p951 : ¬ Nat.Prime 951 := by norm_num
  have c952 : count Nat.Prime 952 = 161 := by rw [count_succ, c951, if_neg p951]
  have p952 : ¬ Nat.Prime 952 := by norm_num
  have c953 : count Nat.Prime 953 = 161 := by rw [count_succ, c952, if_neg p952]
  have p953 : Nat.Prime 953 := by norm_num
  have c954 : count Nat.Prime 954 = 162 := by rw [count_succ, c953, if_pos p953]
  have p954 : ¬ Nat.Prime 954 := by norm_num
  have c955 : count Nat.Prime 955 = 162 := by rw [count_succ, c954, if_neg p954]
  have p955 : ¬ Nat.Prime 955 := by norm_num
  have c956 : count Nat.Prime 956 = 162 := by rw [count_succ, c955, if_neg p955]
  have p956 : ¬ Nat.Prime 956 := by norm_num
  have c957 : count Nat.Prime 957 = 162 := by rw [count_succ, c956, if_neg p956]
  have p957 : ¬ Nat.Prime 957 := by norm_num
  have c958 : count Nat.Prime 958 = 162 := by rw [count_succ, c957, if_neg p957]
  have p958 : ¬ Nat.Prime 958 := by norm_num
  have c959 : count Nat.Prime 959 = 162 := by rw [count_succ, c958, if_neg p958]
  have p959 : ¬ Nat.Prime 959 := by norm_num
  have c960 : count Nat.Prime 960 = 162 := by rw [count_succ, c959, if_neg p959]
  have p960 : ¬ Nat.Prime 960 := by norm_num
  have c961 : count Nat.Prime 961 = 162 := by rw [count_succ, c960, if_neg p960]
  have p961 : ¬ Nat.Prime 961 := by norm_num
  have c962 : count Nat.Prime 962 = 162 := by rw [count_succ, c961, if_neg p961]
  have p962 : ¬ Nat.Prime 962 := by norm_num
  have c963 : count Nat.Prime 963 = 162 := by rw [count_succ, c962, if_neg p962]
  have p963 : ¬ Nat.Prime 963 := by norm_num
  have c964 : count Nat.Prime 964 = 162 := by rw [count_succ, c963, if_neg p963]
  have p964 : ¬ Nat.Prime 964 := by norm_num
  have c965 : count Nat.Prime 965 = 162 := by rw [count_succ, c964, if_neg p964]
  have p965 : ¬ Nat.Prime 965 := by norm_num
  have c966 : count Nat.Prime 966 = 162 := by rw [count_succ, c965, if_neg p965]
  have p966 : ¬ Nat.Prime 966 := by norm_num
  have c967 : count Nat.Prime 967 = 162 := by rw [count_succ, c966, if_neg p966]
  have p967 : Nat.Prime 967 := by norm_num
  have c968 : count Nat.Prime 968 = 163 := by rw [count_succ, c967, if_pos p967]
  have p968 : ¬ Nat.Prime 968 := by norm_num
  have c969 : count Nat.Prime 969 = 163 := by rw [count_succ, c968, if_neg p968]
  have p969 : ¬ Nat.Prime 969 := by norm_num
  have c970 : count Nat.Prime 970 = 163 := by rw [count_succ, c969, if_neg p969]
  have p970 : ¬ Nat.Prime 970 := by norm_num
  have c971 : count Nat.Prime 971 = 163 := by rw [count_succ, c970, if_neg p970]
  have p971 : Nat.Prime 971 := by norm_num
  have c972 : count Nat.Prime 972 = 164 := by rw [count_succ, c971, if_pos p971]
  have p972 : ¬ Nat.Prime 972 := by norm_num
  have c973 : count Nat.Prime 973 = 164 := by rw [count_succ, c972, if_neg p972]
  have p973 : ¬ Nat.Prime 973 := by norm_num
  have c974 : count Nat.Prime 974 = 164 := by rw [count_succ, c973, if_neg p973]
  have p974 : ¬ Nat.Prime 974 := by norm_num
  have c975 : count Nat.Prime 975 = 164 := by rw [count_succ, c974, if_neg p974]
  have p975 : ¬ Nat.Prime 975 := by norm_num
  have c976 : count Nat.Prime 976 = 164 := by rw [count_succ, c975, if_neg p975]
  have p976 : ¬ Nat.Prime 976 := by norm_num
  have c977 : count Nat.Prime 977 = 164 := by rw [count_succ, c976, if_neg p976]
  have p977 : Nat.Prime 977 := by norm_num
  have c978 : count Nat.Prime 978 = 165 := by rw [count_succ, c977, if_pos p977]
  have p978 : ¬ Nat.Prime 978 := by norm_num
  have c979 : count Nat.Prime 979 = 165 := by rw [count_succ, c978, if_neg p978]
  have p979 : ¬ Nat.Prime 979 := by norm_num
  have c980 : count Nat.Prime 980 = 165 := by rw [count_succ, c979, if_neg p979]
  have p980 : ¬ Nat.Prime 980 := by norm_num
  have c981 : count Nat.Prime 981 = 165 := by rw [count_succ, c980, if_neg p980]
  have p981 : ¬ Nat.Prime 981 := by norm_num
  have c982 : count Nat.Prime 982 = 165 := by rw [count_succ, c981, if_neg p981]
  have p982 : ¬ Nat.Prime 982 := by norm_num
  have c983 : count Nat.Prime 983 = 165 := by rw [count_succ, c982, if_neg p982]
  have p983 : Nat.Prime 983 := by norm_num
  have c984 : count Nat.Prime 984 = 166 := by rw [count_succ, c983, if_pos p983]
  have p984 : ¬ Nat.Prime 984 := by norm_num
  have c985 : count Nat.Prime 985 = 166 := by rw [count_succ, c984, if_neg p984]
  have p985 : ¬ Nat.Prime 985 := by norm_num
  have c986 : count Nat.Prime 986 = 166 := by rw [count_succ, c985, if_neg p985]
  have p986 : ¬ Nat.Prime 986 := by norm_num
  have c987 : count Nat.Prime 987 = 166 := by rw [count_succ, c986, if_neg p986]
  have p987 : ¬ Nat.Prime 987 := by norm_num
  have c988 : count Nat.Prime 988 = 166 := by rw [count_succ, c987, if_neg p987]
  have p988 : ¬ Nat.Prime 988 := by norm_num
  have c989 : count Nat.Prime 989 = 166 := by rw [count_succ, c988, if_neg p988]
  have p989 : ¬ Nat.Prime 989 := by norm_num
  have c990 : count Nat.Prime 990 = 166 := by rw [count_succ, c989, if_neg p989]
  have p990 : ¬ Nat.Prime 990 := by norm_num
  have c991 : count Nat.Prime 991 = 166 := by rw [count_succ, c990, if_neg p990]
  have p991 : Nat.Prime 991 := by norm_num
  have c992 : count Nat.Prime 992 = 167 := by rw [count_succ, c991, if_pos p991]
  have p992 : ¬ Nat.Prime 992 := by norm_num
  have c993 : count Nat.Prime 993 = 167 := by rw [count_succ, c992, if_neg p992]
  have p993 : ¬ Nat.Prime 993 := by norm_num
  have c994 : count Nat.Prime 994 = 167 := by rw [count_succ, c993, if_neg p993]
  have p994 : ¬ Nat.Prime 994 := by norm_num
  have c995 : count Nat.Prime 995 = 167 := by rw [count_succ, c994, if_neg p994]
  have p995 : ¬ Nat.Prime 995 := by norm_num
  have c996 : count Nat.Prime 996 = 167 := by rw [count_succ, c995, if_neg p995]
  have p996 : ¬ Nat.Prime 996 := by norm_num
  have c997 : count Nat.Prime 997 = 167 := by rw [count_succ, c996, if_neg p996]
  have p997 : Nat.Prime 997 := by norm_num
  have c998 : count Nat.Prime 998 = 168 := by rw [count_succ, c997, if_pos p997]
  have p998 : ¬ Nat.Prime 998 := by norm_num
  have c999 : count Nat.Prime 999 = 168 := by rw [count_succ, c998, if_neg p998]
  have p999 : ¬ Nat.Prime 999 := by norm_num
  have c1000 : count Nat.Prime 1000 = 168 := by rw [count_succ, c999, if_neg p999]
  exact c1000
