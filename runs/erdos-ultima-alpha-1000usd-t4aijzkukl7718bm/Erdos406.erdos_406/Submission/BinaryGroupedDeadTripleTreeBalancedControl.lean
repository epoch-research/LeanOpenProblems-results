import Submission.BinaryGroupedProfileCertificates

/-! Kernel-checked integer profile certificate, generated from an independently
checked exact table. Its strict-rate status is stated explicitly below. -/
namespace Erdos406GroupedDeadTripleExported
open Erdos406Tropical (Automaton Run)
open Erdos406BinaryAcceptingMinplus
open Erdos406BinaryProfileMinplus
noncomputable section
set_option maxHeartbeats 0
set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 1000000

private inductive TableTree (α : Type) where
  | leaf : α → TableTree α
  | node : ℕ → TableTree α → TableTree α → TableTree α
private def TableTree.lookup {α : Type} : TableTree α → ℕ → α
  | .leaf a, _ => a
  | .node m l r, i => if i < m then TableTree.lookup l i else TableTree.lookup r i

private def nextAtTree : TableTree ((List ℕ)) := (TableTree.node 74 (TableTree.node 37 (TableTree.node 18 (TableTree.node 9 (TableTree.node 4 (TableTree.node 2 (TableTree.node 1 (TableTree.leaf ([0])) (TableTree.leaf ([1]))) (TableTree.node 3 (TableTree.leaf ([2])) (TableTree.leaf ([3,4])))) (TableTree.node 6 (TableTree.node 5 (TableTree.leaf ([5])) (TableTree.leaf ([6,7]))) (TableTree.node 7 (TableTree.leaf ([8])) (TableTree.node 8 (TableTree.leaf ([9,10])) (TableTree.leaf ([11])))))) (TableTree.node 13 (TableTree.node 11 (TableTree.node 10 (TableTree.leaf ([12])) (TableTree.leaf ([13]))) (TableTree.node 12 (TableTree.leaf ([14,15])) (TableTree.leaf ([16])))) (TableTree.node 15 (TableTree.node 14 (TableTree.leaf ([17])) (TableTree.leaf ([18]))) (TableTree.node 16 (TableTree.leaf ([19,20])) (TableTree.node 17 (TableTree.leaf ([21])) (TableTree.leaf ([22,23]))))))) (TableTree.node 27 (TableTree.node 22 (TableTree.node 20 (TableTree.node 19 (TableTree.leaf ([24,25])) (TableTree.leaf ([26]))) (TableTree.node 21 (TableTree.leaf ([27])) (TableTree.leaf ([28,29])))) (TableTree.node 24 (TableTree.node 23 (TableTree.leaf ([30])) (TableTree.leaf ([31]))) (TableTree.node 25 (TableTree.leaf ([32])) (TableTree.node 26 (TableTree.leaf ([33])) (TableTree.leaf ([20])))))) (TableTree.node 32 (TableTree.node 29 (TableTree.node 28 (TableTree.leaf ([34,35])) (TableTree.leaf ([36,37]))) (TableTree.node 30 (TableTree.leaf ([38])) (TableTree.node 31 (TableTree.leaf ([39])) (TableTree.leaf ([19,20]))))) (TableTree.node 34 (TableTree.node 33 (TableTree.leaf ([40])) (TableTree.leaf ([40]))) (TableTree.node 35 (TableTree.leaf ([41])) (TableTree.node 36 (TableTree.leaf ([41])) (TableTree.leaf ([35])))))))) (TableTree.node 55 (TableTree.node 46 (TableTree.node 41 (TableTree.node 39 (TableTree.node 38 (TableTree.leaf ([34,35])) (TableTree.leaf ([42,43]))) (TableTree.node 40 (TableTree.leaf ([43])) (TableTree.leaf ([44])))) (TableTree.node 43 (TableTree.node 42 (TableTree.leaf ([42,44])) (TableTree.leaf ([44]))) (TableTree.node 44 (TableTree.leaf ([42,44])) (TableTree.node 45 (TableTree.leaf ([42,43])) (TableTree.leaf ([45])))))) (TableTree.node 50 (TableTree.node 48 (TableTree.node 47 (TableTree.leaf ([44])) (TableTree.leaf ([46,47]))) (TableTree.node 49 (TableTree.leaf ([48,49])) (TableTree.leaf ([50])))) (TableTree.node 52 (TableTree.node 51 (TableTree.leaf ([51])) (TableTree.leaf ([40]))) (TableTree.node 53 (TableTree.leaf ([52])) (TableTree.node 54 (TableTree.leaf ([53])) (TableTree.leaf ([54]))))))) (TableTree.node 64 (TableTree.node 59 (TableTree.node 57 (TableTree.node 56 (TableTree.leaf ([34,35])) (TableTree.leaf ([55,56]))) (TableTree.node 58 (TableTree.leaf ([57])) (TableTree.leaf ([58])))) (TableTree.node 61 (TableTree.node 60 (TableTree.leaf ([59,60])) (TableTree.leaf ([41]))) (TableTree.node 62 (TableTree.leaf ([41])) (TableTree.node 63 (TableTree.leaf ([41])) (TableTree.leaf ([61])))))) (TableTree.node 69 (TableTree.node 66 (TableTree.node 65 (TableTree.leaf ([62])) (TableTree.leaf ([40]))) (TableTree.node 67 (TableTree.leaf ([63])) (TableTree.node 68 (TableTree.leaf ([53])) (TableTree.leaf ([19,38]))))) (TableTree.node 71 (TableTree.node 70 (TableTree.leaf ([43])) (TableTree.leaf ([20]))) (TableTree.node 72 (TableTree.leaf ([42,44])) (TableTree.node 73 (TableTree.leaf ([64,65])) (TableTree.leaf ([66]))))))))) (TableTree.node 111 (TableTree.node 92 (TableTree.node 83 (TableTree.node 78 (TableTree.node 76 (TableTree.node 75 (TableTree.leaf ([67])) (TableTree.leaf ([30]))) (TableTree.node 77 (TableTree.leaf ([68])) (TableTree.leaf ([41])))) (TableTree.node 80 (TableTree.node 79 (TableTree.leaf ([69])) (TableTree.leaf ([21,70]))) (TableTree.node 81 (TableTree.leaf ([17])) (TableTree.node 82 (TableTree.leaf ([41])) (TableTree.leaf ([41,72])))))) (TableTree.node 87 (TableTree.node 85 (TableTree.node 84 (TableTree.leaf ([41,72])) (TableTree.leaf ([42,43,72]))) (TableTree.node 86 (TableTree.leaf ([43,72])) (TableTree.leaf ([68,72])))) (TableTree.node 89 (TableTree.node 88 (TableTree.leaf ([41,72])) (TableTree.leaf ([44,72]))) (TableTree.node 90 (TableTree.leaf ([42,44,72])) (TableTree.node 91 (TableTree.leaf ([68])) (TableTree.leaf ([41]))))))) (TableTree.node 101 (TableTree.node 96 (TableTree.node 94 (TableTree.node 93 (TableTree.leaf ([42,43])) (TableTree.leaf ([43]))) (TableTree.node 95 (TableTree.leaf ([44])) (TableTree.leaf ([42,44])))) (TableTree.node 98 (TableTree.node 97 (TableTree.leaf ([19,38])) (TableTree.leaf ([43]))) (TableTree.node 99 (TableTree.leaf ([71])) (TableTree.node 100 (TableTree.leaf ([41])) (TableTree.leaf ([71])))))) (TableTree.node 106 (TableTree.node 103 (TableTree.node 102 (TableTree.leaf ([41])) (TableTree.leaf ([17]))) (TableTree.node 104 (TableTree.leaf ([41])) (TableTree.node 105 (TableTree.leaf ([41])) (TableTree.leaf ([41]))))) (TableTree.node 108 (TableTree.node 107 (TableTree.leaf ([41])) (TableTree.leaf ([41]))) (TableTree.node 109 (TableTree.leaf ([20])) (TableTree.node 110 (TableTree.leaf ([42,44])) (TableTree.leaf ([42,43])))))))) (TableTree.node 129 (TableTree.node 120 (TableTree.node 115 (TableTree.node 113 (TableTree.node 112 (TableTree.leaf ([43])) (TableTree.leaf ([68]))) (TableTree.node 114 (TableTree.leaf ([41])) (TableTree.leaf ([68])))) (TableTree.node 117 (TableTree.node 116 (TableTree.leaf ([41])) (TableTree.leaf ([44]))) (TableTree.node 118 (TableTree.leaf ([42,44])) (TableTree.node 119 (TableTree.leaf ([42,43])) (TableTree.leaf ([43])))))) (TableTree.node 124 (TableTree.node 122 (TableTree.node 121 (TableTree.leaf ([44])) (TableTree.leaf ([42,44]))) (TableTree.node 123 (TableTree.leaf ([41])) (TableTree.leaf ([41])))) (TableTree.node 126 (TableTree.node 125 (TableTree.leaf ([17])) (TableTree.leaf ([41]))) (TableTree.node 127 (TableTree.leaf ([41])) (TableTree.node 128 (TableTree.leaf ([41])) (TableTree.leaf ([42,43]))))))) (TableTree.node 138 (TableTree.node 133 (TableTree.node 131 (TableTree.node 130 (TableTree.leaf ([43])) (TableTree.leaf ([68]))) (TableTree.node 132 (TableTree.leaf ([41])) (TableTree.leaf ([68])))) (TableTree.node 135 (TableTree.node 134 (TableTree.leaf ([41])) (TableTree.leaf ([41]))) (TableTree.node 136 (TableTree.leaf ([41])) (TableTree.node 137 (TableTree.leaf ([41,72])) (TableTree.leaf ([41,72])))))) (TableTree.node 143 (TableTree.node 140 (TableTree.node 139 (TableTree.leaf ([44])) (TableTree.leaf ([42,44]))) (TableTree.node 141 (TableTree.leaf ([42,43])) (TableTree.node 142 (TableTree.leaf ([43])) (TableTree.leaf ([41]))))) (TableTree.node 145 (TableTree.node 144 (TableTree.leaf ([41])) (TableTree.leaf ([72]))) (TableTree.node 146 (TableTree.leaf ([72])) (TableTree.node 147 (TableTree.leaf ([44,72])) (TableTree.leaf ([44,72]))))))))))
private def nextAt (i : ℕ) : (List ℕ) := if i < 148 then TableTree.lookup nextAtTree i else []
private def weightAtTree : TableTree ((Array (ℤ))) := (TableTree.node 37 (TableTree.node 18 (TableTree.node 9 (TableTree.node 4 (TableTree.node 2 (TableTree.node 1 (TableTree.leaf (#[0,0,0,2901000,2901000,2901000])) (TableTree.leaf (#[1443599,1443599,1443599,2901000,3093000,3093000]))) (TableTree.node 3 (TableTree.leaf (#[1458000,1458000,1458000,2205000,2013599,2013599])) (TableTree.leaf (#[1000797,1000797,1000797,1539000,1444797,1444797])))) (TableTree.node 6 (TableTree.node 5 (TableTree.leaf (#[1000797,1000797,1000797,1444797,1444797,1444797])) (TableTree.leaf (#[1777797,1777797,1777797,3093000,2998797,2998797]))) (TableTree.node 7 (TableTree.leaf (#[2443799,2443799,2443799,1999798,1999798,1999798])) (TableTree.node 8 (TableTree.leaf (#[2443797,2443797,2443797,2094000,1999797,1999797])) (TableTree.leaf (#[1999797,1999797,1999797,2094000,1999797,1999797])))))) (TableTree.node 13 (TableTree.node 11 (TableTree.node 10 (TableTree.leaf (#[1777794,1777800,1777800,1999799,1999799,1999799])) (TableTree.leaf (#[1777797,1777797,1777797,2094000,1999797,1999797]))) (TableTree.node 12 (TableTree.leaf (#[1999797,1999797,1999797,1999797,1999797,1999797])) (TableTree.leaf (#[1777797,1777797,1777797,1999797,1999797,1999797])))) (TableTree.node 15 (TableTree.node 14 (TableTree.leaf (#[1777797,1777797,1777797,2094000,1999797,1999797])) (TableTree.leaf (#[889794,889800,889800,1000799,1000799,1000799]))) (TableTree.node 16 (TableTree.leaf (#[889797,889797,889797,1095000,1000797,1000797])) (TableTree.node 17 (TableTree.leaf (#[1222794,1222794,1222794,1333795,1333795,1333795])) (TableTree.leaf (#[1888797,1888797,1888797,1999797,1999797,1999797]))))))) (TableTree.node 27 (TableTree.node 22 (TableTree.node 20 (TableTree.node 19 (TableTree.leaf (#[1222797,1222797,1222797,1428000,1333797,1333797])) (TableTree.leaf (#[1888794,1888800,1888800,1999799,1999799,1999799]))) (TableTree.node 21 (TableTree.leaf (#[1888797,1888797,1888797,2094000,1999797,1999797])) (TableTree.leaf (#[1666797,1666797,1666797,1872000,1777797,1777797])))) (TableTree.node 24 (TableTree.node 23 (TableTree.leaf (#[1888794,1888800,1888800,2998799,2998799,2998799])) (TableTree.leaf (#[1888797,1888797,1888797,3093000,2998797,2998797]))) (TableTree.node 25 (TableTree.leaf (#[2776794,2776800,2776800,1999799,1999799,1999799])) (TableTree.node 26 (TableTree.leaf (#[2776799,2776799,2776799,1999798,1999798,1999798])) (TableTree.leaf (#[2554799,2554799,2554799,2554798,2554798,2554798])))))) (TableTree.node 32 (TableTree.node 29 (TableTree.node 28 (TableTree.leaf (#[2776797,2776797,2776797,2094000,1999797,1999797])) (TableTree.leaf (#[2554794,2554800,2554800,2554799,2554799,2554799]))) (TableTree.node 30 (TableTree.leaf (#[2554797,2554797,2554797,2649000,2554797,2554797])) (TableTree.node 31 (TableTree.leaf (#[1666797,1666797,1666797,1777797,1777797,1777797])) (TableTree.leaf (#[1888797,1888797,1888797,2998797,2998797,2998797]))))) (TableTree.node 34 (TableTree.node 33 (TableTree.leaf (#[2776797,2776797,2776797,1999797,1999797,1999797])) (TableTree.leaf (#[2554797,2554797,2554797,2554797,2554797,2554797]))) (TableTree.node 35 (TableTree.leaf (#[1777794,1777800,1777800,1888799,1888799,1888799])) (TableTree.node 36 (TableTree.leaf (#[1777797,1777797,1777797,1983000,1888797,1888797])) (TableTree.leaf (#[2110794,2110800,2110800,2110799,2110799,2110799])))))))) (TableTree.node 55 (TableTree.node 46 (TableTree.node 41 (TableTree.node 39 (TableTree.node 38 (TableTree.leaf (#[2110799,2110799,2110799,2110798,2110798,2110798])) (TableTree.leaf (#[1888799,1888799,1888799,1999798,1999798,1999798]))) (TableTree.node 40 (TableTree.leaf (#[2110797,2110797,2110797,2110797,2205000,2205000])) (TableTree.leaf (#[1777797,1777797,1777797,1888797,1888797,1888797])))) (TableTree.node 43 (TableTree.node 42 (TableTree.leaf (#[1888797,0,0,1888797,0,0])) (TableTree.leaf (#[1888794,1888800,0,1888799,0,0]))) (TableTree.node 44 (TableTree.leaf (#[1888799,0,0,1888798,0,0])) (TableTree.node 45 (TableTree.leaf (#[1888797,0,0,1983000,1888797,0])) (TableTree.leaf (#[889799,889799,889799,889798,889798,889798])))))) (TableTree.node 50 (TableTree.node 48 (TableTree.node 47 (TableTree.leaf (#[889794,889800,889800,889799,889799,889799])) (TableTree.leaf (#[889797,889797,889797,984000,889797,889797]))) (TableTree.node 49 (TableTree.leaf (#[889794,889800,889800,1000799,1000799,1000799])) (TableTree.leaf (#[889799,889799,889799,1000798,1000798,1000798])))) (TableTree.node 52 (TableTree.node 51 (TableTree.leaf (#[1777799,1777799,1777799,1888798,1888798,1888798])) (TableTree.leaf (#[889794,889794,889794,1000795,1000795,1000795]))) (TableTree.node 53 (TableTree.leaf (#[1111794,1111794,1111794,1222795,1222795,1222795])) (TableTree.node 54 (TableTree.leaf (#[1222797,1222797,1222797,1222797,1222797,1222797])) (TableTree.leaf (#[889797,889797,889797,1095000,1000797,1000797]))))))) (TableTree.node 64 (TableTree.node 59 (TableTree.node 57 (TableTree.node 56 (TableTree.leaf (#[1111794,1111800,1111800,1222799,1222799,1222799])) (TableTree.leaf (#[1111799,1111799,1111799,1222798,1222798,1222798]))) (TableTree.node 58 (TableTree.leaf (#[1222799,1222799,1222799,1222798,1222798,1222798])) (TableTree.leaf (#[1111797,1111797,1111797,1317000,1222797,1222797])))) (TableTree.node 61 (TableTree.node 60 (TableTree.leaf (#[1222794,1222800,1222800,1222799,1222799,1222799])) (TableTree.leaf (#[1222797,1222797,1222797,1317000,1222797,1222797]))) (TableTree.node 62 (TableTree.leaf (#[889797,889797,889797,889797,889797,889797])) (TableTree.node 63 (TableTree.leaf (#[889797,889797,889797,1000797,1000797,1000797])) (TableTree.leaf (#[1111797,1111797,1111797,1222797,1222797,1222797])))))) (TableTree.node 69 (TableTree.node 66 (TableTree.node 65 (TableTree.leaf (#[1666794,1666800,1666800,1666799,1666799,1666799])) (TableTree.leaf (#[1666799,1666799,1666799,1666798,1666798,1666798]))) (TableTree.node 67 (TableTree.leaf (#[1666799,1666799,1666799,1777798,1777798,1777798])) (TableTree.node 68 (TableTree.leaf (#[1666794,1666794,1666794,1666795,1666795,1666795])) (TableTree.leaf (#[1888794,0,0,1888795,0,0]))))) (TableTree.node 71 (TableTree.node 70 (TableTree.leaf (#[1666797,1666797,1666797,1761000,1666797,1666797])) (TableTree.leaf (#[1666794,1666800,1666800,1777799,1777799,1777799]))) (TableTree.node 72 (TableTree.leaf (#[1888794,1888794,1888794,1999795,1999795,1999795])) (TableTree.node 73 (TableTree.leaf (#[0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0])))))))))
private def weightAt (i : ℕ) : (Array (ℤ)) := if i < 74 then TableTree.lookup weightAtTree i else #[]
private def sourceAtTree : TableTree (ℕ) := (TableTree.node 464 (TableTree.node 232 (TableTree.node 116 (TableTree.node 58 (TableTree.node 29 (TableTree.node 14 (TableTree.node 7 (TableTree.node 3 (TableTree.node 1 (TableTree.leaf (0)) (TableTree.node 2 (TableTree.leaf (0)) (TableTree.leaf (0)))) (TableTree.node 5 (TableTree.node 4 (TableTree.leaf (0)) (TableTree.leaf (0))) (TableTree.node 6 (TableTree.leaf (0)) (TableTree.leaf (0))))) (TableTree.node 10 (TableTree.node 8 (TableTree.leaf (0)) (TableTree.node 9 (TableTree.leaf (0)) (TableTree.leaf (1)))) (TableTree.node 12 (TableTree.node 11 (TableTree.leaf (1)) (TableTree.leaf (1))) (TableTree.node 13 (TableTree.leaf (1)) (TableTree.leaf (1)))))) (TableTree.node 21 (TableTree.node 17 (TableTree.node 15 (TableTree.leaf (1)) (TableTree.node 16 (TableTree.leaf (1)) (TableTree.leaf (1)))) (TableTree.node 19 (TableTree.node 18 (TableTree.leaf (1)) (TableTree.leaf (2))) (TableTree.node 20 (TableTree.leaf (2)) (TableTree.leaf (2))))) (TableTree.node 25 (TableTree.node 23 (TableTree.node 22 (TableTree.leaf (2)) (TableTree.leaf (2))) (TableTree.node 24 (TableTree.leaf (2)) (TableTree.leaf (2)))) (TableTree.node 27 (TableTree.node 26 (TableTree.leaf (2)) (TableTree.leaf (2))) (TableTree.node 28 (TableTree.leaf (3)) (TableTree.leaf (4))))))) (TableTree.node 43 (TableTree.node 36 (TableTree.node 32 (TableTree.node 30 (TableTree.leaf (3)) (TableTree.node 31 (TableTree.leaf (4)) (TableTree.leaf (3)))) (TableTree.node 34 (TableTree.node 33 (TableTree.leaf (4)) (TableTree.leaf (3))) (TableTree.node 35 (TableTree.leaf (4)) (TableTree.leaf (3))))) (TableTree.node 39 (TableTree.node 37 (TableTree.leaf (4)) (TableTree.node 38 (TableTree.leaf (3)) (TableTree.leaf (4)))) (TableTree.node 41 (TableTree.node 40 (TableTree.leaf (3)) (TableTree.leaf (4))) (TableTree.node 42 (TableTree.leaf (3)) (TableTree.leaf (4)))))) (TableTree.node 50 (TableTree.node 46 (TableTree.node 44 (TableTree.leaf (3)) (TableTree.node 45 (TableTree.leaf (4)) (TableTree.leaf (5)))) (TableTree.node 48 (TableTree.node 47 (TableTree.leaf (5)) (TableTree.leaf (5))) (TableTree.node 49 (TableTree.leaf (5)) (TableTree.leaf (5))))) (TableTree.node 54 (TableTree.node 52 (TableTree.node 51 (TableTree.leaf (5)) (TableTree.leaf (5))) (TableTree.node 53 (TableTree.leaf (5)) (TableTree.leaf (5)))) (TableTree.node 56 (TableTree.node 55 (TableTree.leaf (6)) (TableTree.leaf (7))) (TableTree.node 57 (TableTree.leaf (6)) (TableTree.leaf (7)))))))) (TableTree.node 87 (TableTree.node 72 (TableTree.node 65 (TableTree.node 61 (TableTree.node 59 (TableTree.leaf (6)) (TableTree.node 60 (TableTree.leaf (7)) (TableTree.leaf (6)))) (TableTree.node 63 (TableTree.node 62 (TableTree.leaf (7)) (TableTree.leaf (6))) (TableTree.node 64 (TableTree.leaf (7)) (TableTree.leaf (6))))) (TableTree.node 68 (TableTree.node 66 (TableTree.leaf (7)) (TableTree.node 67 (TableTree.leaf (6)) (TableTree.leaf (7)))) (TableTree.node 70 (TableTree.node 69 (TableTree.leaf (6)) (TableTree.leaf (7))) (TableTree.node 71 (TableTree.leaf (6)) (TableTree.leaf (7)))))) (TableTree.node 79 (TableTree.node 75 (TableTree.node 73 (TableTree.leaf (8)) (TableTree.node 74 (TableTree.leaf (8)) (TableTree.leaf (11)))) (TableTree.node 77 (TableTree.node 76 (TableTree.leaf (11)) (TableTree.leaf (8))) (TableTree.node 78 (TableTree.leaf (8)) (TableTree.leaf (11))))) (TableTree.node 83 (TableTree.node 81 (TableTree.node 80 (TableTree.leaf (11)) (TableTree.leaf (8))) (TableTree.node 82 (TableTree.leaf (8)) (TableTree.leaf (11)))) (TableTree.node 85 (TableTree.node 84 (TableTree.leaf (11)) (TableTree.leaf (8))) (TableTree.node 86 (TableTree.leaf (8)) (TableTree.leaf (11))))))) (TableTree.node 101 (TableTree.node 94 (TableTree.node 90 (TableTree.node 88 (TableTree.leaf (11)) (TableTree.node 89 (TableTree.leaf (8)) (TableTree.leaf (9)))) (TableTree.node 92 (TableTree.node 91 (TableTree.leaf (10)) (TableTree.leaf (11))) (TableTree.node 93 (TableTree.leaf (12)) (TableTree.leaf (9))))) (TableTree.node 97 (TableTree.node 95 (TableTree.leaf (10)) (TableTree.node 96 (TableTree.leaf (9)) (TableTree.leaf (10)))) (TableTree.node 99 (TableTree.node 98 (TableTree.leaf (12)) (TableTree.leaf (12))) (TableTree.node 100 (TableTree.leaf (9)) (TableTree.leaf (10)))))) (TableTree.node 108 (TableTree.node 104 (TableTree.node 102 (TableTree.leaf (9)) (TableTree.node 103 (TableTree.leaf (10)) (TableTree.leaf (12)))) (TableTree.node 106 (TableTree.node 105 (TableTree.leaf (12)) (TableTree.leaf (9))) (TableTree.node 107 (TableTree.leaf (10)) (TableTree.leaf (9))))) (TableTree.node 112 (TableTree.node 110 (TableTree.node 109 (TableTree.leaf (10)) (TableTree.leaf (12))) (TableTree.node 111 (TableTree.leaf (12)) (TableTree.leaf (9)))) (TableTree.node 114 (TableTree.node 113 (TableTree.leaf (10)) (TableTree.leaf (9))) (TableTree.node 115 (TableTree.leaf (10)) (TableTree.leaf (12))))))))) (TableTree.node 174 (TableTree.node 145 (TableTree.node 130 (TableTree.node 123 (TableTree.node 119 (TableTree.node 117 (TableTree.leaf (12)) (TableTree.node 118 (TableTree.leaf (13)) (TableTree.leaf (13)))) (TableTree.node 121 (TableTree.node 120 (TableTree.leaf (13)) (TableTree.leaf (13))) (TableTree.node 122 (TableTree.leaf (13)) (TableTree.leaf (13))))) (TableTree.node 126 (TableTree.node 124 (TableTree.leaf (13)) (TableTree.node 125 (TableTree.leaf (13)) (TableTree.leaf (13)))) (TableTree.node 128 (TableTree.node 127 (TableTree.leaf (14)) (TableTree.leaf (15))) (TableTree.node 129 (TableTree.leaf (14)) (TableTree.leaf (15)))))) (TableTree.node 137 (TableTree.node 133 (TableTree.node 131 (TableTree.leaf (14)) (TableTree.node 132 (TableTree.leaf (15)) (TableTree.leaf (14)))) (TableTree.node 135 (TableTree.node 134 (TableTree.leaf (15)) (TableTree.leaf (14))) (TableTree.node 136 (TableTree.leaf (15)) (TableTree.leaf (14))))) (TableTree.node 141 (TableTree.node 139 (TableTree.node 138 (TableTree.leaf (15)) (TableTree.leaf (14))) (TableTree.node 140 (TableTree.leaf (15)) (TableTree.leaf (14)))) (TableTree.node 143 (TableTree.node 142 (TableTree.leaf (15)) (TableTree.leaf (14))) (TableTree.node 144 (TableTree.leaf (15)) (TableTree.leaf (16))))))) (TableTree.node 159 (TableTree.node 152 (TableTree.node 148 (TableTree.node 146 (TableTree.leaf (16)) (TableTree.node 147 (TableTree.leaf (18)) (TableTree.leaf (18)))) (TableTree.node 150 (TableTree.node 149 (TableTree.leaf (16)) (TableTree.leaf (16))) (TableTree.node 151 (TableTree.leaf (18)) (TableTree.leaf (18))))) (TableTree.node 155 (TableTree.node 153 (TableTree.leaf (16)) (TableTree.node 154 (TableTree.leaf (16)) (TableTree.leaf (18)))) (TableTree.node 157 (TableTree.node 156 (TableTree.leaf (18)) (TableTree.leaf (16))) (TableTree.node 158 (TableTree.leaf (16)) (TableTree.leaf (18)))))) (TableTree.node 166 (TableTree.node 162 (TableTree.node 160 (TableTree.leaf (18)) (TableTree.node 161 (TableTree.leaf (16)) (TableTree.leaf (17)))) (TableTree.node 164 (TableTree.node 163 (TableTree.leaf (18)) (TableTree.leaf (19))) (TableTree.node 165 (TableTree.leaf (20)) (TableTree.leaf (17))))) (TableTree.node 170 (TableTree.node 168 (TableTree.node 167 (TableTree.leaf (17)) (TableTree.leaf (19))) (TableTree.node 169 (TableTree.leaf (20)) (TableTree.leaf (19)))) (TableTree.node 172 (TableTree.node 171 (TableTree.leaf (20)) (TableTree.leaf (17))) (TableTree.node 173 (TableTree.leaf (17)) (TableTree.leaf (19)))))))) (TableTree.node 203 (TableTree.node 188 (TableTree.node 181 (TableTree.node 177 (TableTree.node 175 (TableTree.leaf (20)) (TableTree.node 176 (TableTree.leaf (19)) (TableTree.leaf (20)))) (TableTree.node 179 (TableTree.node 178 (TableTree.leaf (17)) (TableTree.leaf (17))) (TableTree.node 180 (TableTree.leaf (19)) (TableTree.leaf (20))))) (TableTree.node 184 (TableTree.node 182 (TableTree.leaf (19)) (TableTree.node 183 (TableTree.leaf (20)) (TableTree.leaf (17)))) (TableTree.node 186 (TableTree.node 185 (TableTree.leaf (17)) (TableTree.leaf (19))) (TableTree.node 187 (TableTree.leaf (20)) (TableTree.leaf (19)))))) (TableTree.node 195 (TableTree.node 191 (TableTree.node 189 (TableTree.leaf (20)) (TableTree.node 190 (TableTree.leaf (21)) (TableTree.leaf (21)))) (TableTree.node 193 (TableTree.node 192 (TableTree.leaf (21)) (TableTree.leaf (21))) (TableTree.node 194 (TableTree.leaf (30)) (TableTree.leaf (30))))) (TableTree.node 199 (TableTree.node 197 (TableTree.node 196 (TableTree.leaf (30)) (TableTree.leaf (30))) (TableTree.node 198 (TableTree.leaf (21)) (TableTree.leaf (21)))) (TableTree.node 201 (TableTree.node 200 (TableTree.leaf (21)) (TableTree.leaf (21))) (TableTree.node 202 (TableTree.leaf (30)) (TableTree.leaf (30))))))) (TableTree.node 217 (TableTree.node 210 (TableTree.node 206 (TableTree.node 204 (TableTree.leaf (30)) (TableTree.node 205 (TableTree.leaf (30)) (TableTree.leaf (21)))) (TableTree.node 208 (TableTree.node 207 (TableTree.leaf (22)) (TableTree.leaf (23))) (TableTree.node 209 (TableTree.leaf (22)) (TableTree.leaf (23))))) (TableTree.node 213 (TableTree.node 211 (TableTree.leaf (22)) (TableTree.node 212 (TableTree.leaf (23)) (TableTree.leaf (30)))) (TableTree.node 215 (TableTree.node 214 (TableTree.leaf (31)) (TableTree.leaf (31))) (TableTree.node 216 (TableTree.leaf (31)) (TableTree.leaf (22)))))) (TableTree.node 224 (TableTree.node 220 (TableTree.node 218 (TableTree.leaf (23)) (TableTree.node 219 (TableTree.leaf (22)) (TableTree.leaf (23)))) (TableTree.node 222 (TableTree.node 221 (TableTree.leaf (22)) (TableTree.leaf (23))) (TableTree.node 223 (TableTree.leaf (22)) (TableTree.leaf (23))))) (TableTree.node 228 (TableTree.node 226 (TableTree.node 225 (TableTree.leaf (31)) (TableTree.leaf (31))) (TableTree.node 227 (TableTree.leaf (31)) (TableTree.leaf (31)))) (TableTree.node 230 (TableTree.node 229 (TableTree.leaf (22)) (TableTree.leaf (23))) (TableTree.node 231 (TableTree.leaf (22)) (TableTree.leaf (23)))))))))) (TableTree.node 348 (TableTree.node 290 (TableTree.node 261 (TableTree.node 246 (TableTree.node 239 (TableTree.node 235 (TableTree.node 233 (TableTree.leaf (24)) (TableTree.node 234 (TableTree.leaf (25)) (TableTree.leaf (24)))) (TableTree.node 237 (TableTree.node 236 (TableTree.leaf (25)) (TableTree.leaf (27))) (TableTree.node 238 (TableTree.leaf (27)) (TableTree.leaf (31))))) (TableTree.node 242 (TableTree.node 240 (TableTree.leaf (31)) (TableTree.node 241 (TableTree.leaf (32)) (TableTree.leaf (32)))) (TableTree.node 244 (TableTree.node 243 (TableTree.leaf (24)) (TableTree.leaf (25))) (TableTree.node 245 (TableTree.leaf (24)) (TableTree.leaf (25)))))) (TableTree.node 253 (TableTree.node 249 (TableTree.node 247 (TableTree.leaf (27)) (TableTree.node 248 (TableTree.leaf (27)) (TableTree.leaf (24)))) (TableTree.node 251 (TableTree.node 250 (TableTree.leaf (25)) (TableTree.leaf (24))) (TableTree.node 252 (TableTree.leaf (25)) (TableTree.leaf (27))))) (TableTree.node 257 (TableTree.node 255 (TableTree.node 254 (TableTree.leaf (27)) (TableTree.leaf (32))) (TableTree.node 256 (TableTree.leaf (32)) (TableTree.leaf (32)))) (TableTree.node 259 (TableTree.node 258 (TableTree.leaf (32)) (TableTree.leaf (24))) (TableTree.node 260 (TableTree.leaf (25)) (TableTree.leaf (24))))))) (TableTree.node 275 (TableTree.node 268 (TableTree.node 264 (TableTree.node 262 (TableTree.leaf (25)) (TableTree.node 263 (TableTree.leaf (27)) (TableTree.leaf (27)))) (TableTree.node 266 (TableTree.node 265 (TableTree.leaf (24)) (TableTree.leaf (25))) (TableTree.node 267 (TableTree.leaf (26)) (TableTree.leaf (27))))) (TableTree.node 271 (TableTree.node 269 (TableTree.leaf (28)) (TableTree.node 270 (TableTree.leaf (29)) (TableTree.leaf (32)))) (TableTree.node 273 (TableTree.node 272 (TableTree.leaf (32)) (TableTree.leaf (32))) (TableTree.node 274 (TableTree.leaf (33)) (TableTree.leaf (26)))))) (TableTree.node 282 (TableTree.node 278 (TableTree.node 276 (TableTree.leaf (26)) (TableTree.node 277 (TableTree.leaf (28)) (TableTree.leaf (29)))) (TableTree.node 280 (TableTree.node 279 (TableTree.leaf (28)) (TableTree.leaf (29))) (TableTree.node 281 (TableTree.leaf (26)) (TableTree.leaf (26))))) (TableTree.node 286 (TableTree.node 284 (TableTree.node 283 (TableTree.leaf (28)) (TableTree.leaf (29))) (TableTree.node 285 (TableTree.leaf (28)) (TableTree.leaf (29)))) (TableTree.node 288 (TableTree.node 287 (TableTree.leaf (33)) (TableTree.leaf (33))) (TableTree.node 289 (TableTree.leaf (33)) (TableTree.leaf (33)))))))) (TableTree.node 319 (TableTree.node 304 (TableTree.node 297 (TableTree.node 293 (TableTree.node 291 (TableTree.leaf (26)) (TableTree.node 292 (TableTree.leaf (26)) (TableTree.leaf (28)))) (TableTree.node 295 (TableTree.node 294 (TableTree.leaf (29)) (TableTree.leaf (28))) (TableTree.node 296 (TableTree.leaf (29)) (TableTree.leaf (26))))) (TableTree.node 300 (TableTree.node 298 (TableTree.leaf (26)) (TableTree.node 299 (TableTree.leaf (28)) (TableTree.leaf (29)))) (TableTree.node 302 (TableTree.node 301 (TableTree.leaf (28)) (TableTree.leaf (29))) (TableTree.node 303 (TableTree.leaf (33)) (TableTree.leaf (33)))))) (TableTree.node 311 (TableTree.node 307 (TableTree.node 305 (TableTree.leaf (33)) (TableTree.node 306 (TableTree.leaf (33)) (TableTree.leaf (34)))) (TableTree.node 309 (TableTree.node 308 (TableTree.leaf (35)) (TableTree.leaf (34))) (TableTree.node 310 (TableTree.leaf (35)) (TableTree.leaf (34))))) (TableTree.node 315 (TableTree.node 313 (TableTree.node 312 (TableTree.leaf (35)) (TableTree.leaf (34))) (TableTree.node 314 (TableTree.leaf (35)) (TableTree.leaf (34)))) (TableTree.node 317 (TableTree.node 316 (TableTree.leaf (35)) (TableTree.leaf (34))) (TableTree.node 318 (TableTree.leaf (35)) (TableTree.leaf (34))))))) (TableTree.node 333 (TableTree.node 326 (TableTree.node 322 (TableTree.node 320 (TableTree.leaf (35)) (TableTree.node 321 (TableTree.leaf (34)) (TableTree.leaf (35)))) (TableTree.node 324 (TableTree.node 323 (TableTree.leaf (34)) (TableTree.leaf (35))) (TableTree.node 325 (TableTree.leaf (36)) (TableTree.leaf (37))))) (TableTree.node 329 (TableTree.node 327 (TableTree.leaf (36)) (TableTree.node 328 (TableTree.leaf (37)) (TableTree.leaf (39)))) (TableTree.node 331 (TableTree.node 330 (TableTree.leaf (39)) (TableTree.leaf (36))) (TableTree.node 332 (TableTree.leaf (37)) (TableTree.leaf (36)))))) (TableTree.node 340 (TableTree.node 336 (TableTree.node 334 (TableTree.leaf (37)) (TableTree.node 335 (TableTree.leaf (39)) (TableTree.leaf (39)))) (TableTree.node 338 (TableTree.node 337 (TableTree.leaf (36)) (TableTree.leaf (37))) (TableTree.node 339 (TableTree.leaf (36)) (TableTree.leaf (37))))) (TableTree.node 344 (TableTree.node 342 (TableTree.node 341 (TableTree.leaf (39)) (TableTree.leaf (39))) (TableTree.node 343 (TableTree.leaf (36)) (TableTree.leaf (37)))) (TableTree.node 346 (TableTree.node 345 (TableTree.leaf (36)) (TableTree.leaf (37))) (TableTree.node 347 (TableTree.leaf (39)) (TableTree.leaf (39))))))))) (TableTree.node 406 (TableTree.node 377 (TableTree.node 362 (TableTree.node 355 (TableTree.node 351 (TableTree.node 349 (TableTree.leaf (36)) (TableTree.node 350 (TableTree.leaf (37)) (TableTree.leaf (38)))) (TableTree.node 353 (TableTree.node 352 (TableTree.leaf (39)) (TableTree.leaf (38))) (TableTree.node 354 (TableTree.leaf (38)) (TableTree.leaf (38))))) (TableTree.node 358 (TableTree.node 356 (TableTree.leaf (38)) (TableTree.node 357 (TableTree.leaf (38)) (TableTree.leaf (38)))) (TableTree.node 360 (TableTree.node 359 (TableTree.leaf (38)) (TableTree.leaf (38))) (TableTree.node 361 (TableTree.leaf (40)) (TableTree.leaf (40)))))) (TableTree.node 369 (TableTree.node 365 (TableTree.node 363 (TableTree.leaf (40)) (TableTree.node 364 (TableTree.leaf (40)) (TableTree.leaf (40)))) (TableTree.node 367 (TableTree.node 366 (TableTree.leaf (40)) (TableTree.leaf (40))) (TableTree.node 368 (TableTree.leaf (40)) (TableTree.leaf (40))))) (TableTree.node 373 (TableTree.node 371 (TableTree.node 370 (TableTree.leaf (40)) (TableTree.leaf (40))) (TableTree.node 372 (TableTree.leaf (40)) (TableTree.leaf (40)))) (TableTree.node 375 (TableTree.node 374 (TableTree.leaf (40)) (TableTree.leaf (40))) (TableTree.node 376 (TableTree.leaf (41)) (TableTree.leaf (41))))))) (TableTree.node 391 (TableTree.node 384 (TableTree.node 380 (TableTree.node 378 (TableTree.leaf (42)) (TableTree.node 379 (TableTree.leaf (43)) (TableTree.leaf (42)))) (TableTree.node 382 (TableTree.node 381 (TableTree.leaf (43)) (TableTree.leaf (44))) (TableTree.node 383 (TableTree.leaf (44)) (TableTree.leaf (41))))) (TableTree.node 387 (TableTree.node 385 (TableTree.leaf (41)) (TableTree.node 386 (TableTree.leaf (41)) (TableTree.leaf (41)))) (TableTree.node 389 (TableTree.node 388 (TableTree.leaf (42)) (TableTree.leaf (43))) (TableTree.node 390 (TableTree.leaf (42)) (TableTree.leaf (43)))))) (TableTree.node 398 (TableTree.node 394 (TableTree.node 392 (TableTree.leaf (44)) (TableTree.node 393 (TableTree.leaf (44)) (TableTree.leaf (42)))) (TableTree.node 396 (TableTree.node 395 (TableTree.leaf (43)) (TableTree.leaf (42))) (TableTree.node 397 (TableTree.leaf (43)) (TableTree.leaf (44))))) (TableTree.node 402 (TableTree.node 400 (TableTree.node 399 (TableTree.leaf (44)) (TableTree.leaf (41))) (TableTree.node 401 (TableTree.leaf (41)) (TableTree.leaf (41)))) (TableTree.node 404 (TableTree.node 403 (TableTree.leaf (41)) (TableTree.leaf (42))) (TableTree.node 405 (TableTree.leaf (43)) (TableTree.leaf (42)))))))) (TableTree.node 435 (TableTree.node 420 (TableTree.node 413 (TableTree.node 409 (TableTree.node 407 (TableTree.leaf (43)) (TableTree.node 408 (TableTree.leaf (44)) (TableTree.leaf (44)))) (TableTree.node 411 (TableTree.node 410 (TableTree.leaf (42)) (TableTree.leaf (43))) (TableTree.node 412 (TableTree.leaf (44)) (TableTree.leaf (41))))) (TableTree.node 416 (TableTree.node 414 (TableTree.leaf (41)) (TableTree.node 415 (TableTree.leaf (43)) (TableTree.leaf (43)))) (TableTree.node 418 (TableTree.node 417 (TableTree.leaf (42)) (TableTree.leaf (43))) (TableTree.node 419 (TableTree.leaf (42)) (TableTree.leaf (41)))))) (TableTree.node 427 (TableTree.node 423 (TableTree.node 421 (TableTree.leaf (41)) (TableTree.node 422 (TableTree.leaf (41)) (TableTree.leaf (41)))) (TableTree.node 425 (TableTree.node 424 (TableTree.leaf (43)) (TableTree.leaf (43))) (TableTree.node 426 (TableTree.leaf (42)) (TableTree.leaf (42))))) (TableTree.node 431 (TableTree.node 429 (TableTree.node 428 (TableTree.leaf (43)) (TableTree.leaf (43))) (TableTree.node 430 (TableTree.leaf (41)) (TableTree.leaf (41)))) (TableTree.node 433 (TableTree.node 432 (TableTree.leaf (41)) (TableTree.leaf (41))) (TableTree.node 434 (TableTree.leaf (41)) (TableTree.leaf (41))))))) (TableTree.node 449 (TableTree.node 442 (TableTree.node 438 (TableTree.node 436 (TableTree.leaf (41)) (TableTree.node 437 (TableTree.leaf (41)) (TableTree.leaf (41)))) (TableTree.node 440 (TableTree.node 439 (TableTree.leaf (41)) (TableTree.leaf (45))) (TableTree.node 441 (TableTree.leaf (46)) (TableTree.leaf (47))))) (TableTree.node 445 (TableTree.node 443 (TableTree.leaf (45)) (TableTree.node 444 (TableTree.leaf (45)) (TableTree.leaf (46)))) (TableTree.node 447 (TableTree.node 446 (TableTree.leaf (47)) (TableTree.leaf (46))) (TableTree.node 448 (TableTree.leaf (47)) (TableTree.leaf (45)))))) (TableTree.node 456 (TableTree.node 452 (TableTree.node 450 (TableTree.leaf (45)) (TableTree.node 451 (TableTree.leaf (46)) (TableTree.leaf (47)))) (TableTree.node 454 (TableTree.node 453 (TableTree.leaf (46)) (TableTree.leaf (47))) (TableTree.node 455 (TableTree.leaf (41)) (TableTree.leaf (41))))) (TableTree.node 460 (TableTree.node 458 (TableTree.node 457 (TableTree.leaf (61)) (TableTree.leaf (61))) (TableTree.node 459 (TableTree.leaf (61)) (TableTree.leaf (61)))) (TableTree.node 462 (TableTree.node 461 (TableTree.leaf (61)) (TableTree.leaf (45))) (TableTree.node 463 (TableTree.leaf (45)) (TableTree.leaf (46))))))))))) (TableTree.node 696 (TableTree.node 580 (TableTree.node 522 (TableTree.node 493 (TableTree.node 478 (TableTree.node 471 (TableTree.node 467 (TableTree.node 465 (TableTree.leaf (47)) (TableTree.node 466 (TableTree.leaf (46)) (TableTree.leaf (47)))) (TableTree.node 469 (TableTree.node 468 (TableTree.leaf (45)) (TableTree.leaf (45))) (TableTree.node 470 (TableTree.leaf (46)) (TableTree.leaf (47))))) (TableTree.node 474 (TableTree.node 472 (TableTree.leaf (46)) (TableTree.node 473 (TableTree.leaf (47)) (TableTree.leaf (48)))) (TableTree.node 476 (TableTree.node 475 (TableTree.leaf (49)) (TableTree.leaf (48))) (TableTree.node 477 (TableTree.leaf (49)) (TableTree.leaf (51)))))) (TableTree.node 485 (TableTree.node 481 (TableTree.node 479 (TableTree.leaf (51)) (TableTree.node 480 (TableTree.leaf (48)) (TableTree.leaf (49)))) (TableTree.node 483 (TableTree.node 482 (TableTree.leaf (48)) (TableTree.leaf (49))) (TableTree.node 484 (TableTree.leaf (51)) (TableTree.leaf (51))))) (TableTree.node 489 (TableTree.node 487 (TableTree.node 486 (TableTree.leaf (54)) (TableTree.leaf (54))) (TableTree.node 488 (TableTree.leaf (54)) (TableTree.leaf (54)))) (TableTree.node 491 (TableTree.node 490 (TableTree.leaf (61)) (TableTree.leaf (61))) (TableTree.node 492 (TableTree.leaf (61)) (TableTree.leaf (61))))))) (TableTree.node 507 (TableTree.node 500 (TableTree.node 496 (TableTree.node 494 (TableTree.leaf (62)) (TableTree.node 495 (TableTree.leaf (62)) (TableTree.leaf (62)))) (TableTree.node 498 (TableTree.node 497 (TableTree.leaf (62)) (TableTree.leaf (48))) (TableTree.node 499 (TableTree.leaf (49)) (TableTree.leaf (48))))) (TableTree.node 503 (TableTree.node 501 (TableTree.leaf (49)) (TableTree.node 502 (TableTree.leaf (51)) (TableTree.leaf (51)))) (TableTree.node 505 (TableTree.node 504 (TableTree.leaf (48)) (TableTree.leaf (49))) (TableTree.node 506 (TableTree.leaf (48)) (TableTree.leaf (49)))))) (TableTree.node 514 (TableTree.node 510 (TableTree.node 508 (TableTree.leaf (51)) (TableTree.node 509 (TableTree.leaf (51)) (TableTree.leaf (54)))) (TableTree.node 512 (TableTree.node 511 (TableTree.leaf (54)) (TableTree.leaf (54))) (TableTree.node 513 (TableTree.leaf (54)) (TableTree.leaf (48))))) (TableTree.node 518 (TableTree.node 516 (TableTree.node 515 (TableTree.leaf (49)) (TableTree.leaf (50))) (TableTree.node 517 (TableTree.leaf (51)) (TableTree.leaf (50)))) (TableTree.node 520 (TableTree.node 519 (TableTree.leaf (50)) (TableTree.leaf (40))) (TableTree.node 521 (TableTree.leaf (40)) (TableTree.leaf (54)))))))) (TableTree.node 551 (TableTree.node 536 (TableTree.node 529 (TableTree.node 525 (TableTree.node 523 (TableTree.leaf (62)) (TableTree.node 524 (TableTree.leaf (62)) (TableTree.leaf (62)))) (TableTree.node 527 (TableTree.node 526 (TableTree.leaf (62)) (TableTree.leaf (62))) (TableTree.node 528 (TableTree.leaf (50)) (TableTree.leaf (50))))) (TableTree.node 532 (TableTree.node 530 (TableTree.leaf (50)) (TableTree.node 531 (TableTree.leaf (50)) (TableTree.leaf (40)))) (TableTree.node 534 (TableTree.node 533 (TableTree.leaf (50)) (TableTree.leaf (50))) (TableTree.node 535 (TableTree.leaf (40)) (TableTree.leaf (40)))))) (TableTree.node 543 (TableTree.node 539 (TableTree.node 537 (TableTree.leaf (52)) (TableTree.node 538 (TableTree.leaf (52)) (TableTree.leaf (55)))) (TableTree.node 541 (TableTree.node 540 (TableTree.leaf (56)) (TableTree.leaf (55))) (TableTree.node 542 (TableTree.leaf (56)) (TableTree.leaf (58))))) (TableTree.node 547 (TableTree.node 545 (TableTree.node 544 (TableTree.leaf (58)) (TableTree.leaf (40))) (TableTree.node 546 (TableTree.leaf (40)) (TableTree.leaf (40)))) (TableTree.node 549 (TableTree.node 548 (TableTree.leaf (40)) (TableTree.leaf (40))) (TableTree.node 550 (TableTree.leaf (40)) (TableTree.leaf (63))))))) (TableTree.node 565 (TableTree.node 558 (TableTree.node 554 (TableTree.node 552 (TableTree.leaf (63)) (TableTree.node 553 (TableTree.leaf (52)) (TableTree.leaf (52)))) (TableTree.node 556 (TableTree.node 555 (TableTree.leaf (52)) (TableTree.leaf (52))) (TableTree.node 557 (TableTree.leaf (55)) (TableTree.leaf (56))))) (TableTree.node 561 (TableTree.node 559 (TableTree.leaf (55)) (TableTree.node 560 (TableTree.leaf (56)) (TableTree.leaf (58)))) (TableTree.node 563 (TableTree.node 562 (TableTree.leaf (58)) (TableTree.leaf (55))) (TableTree.node 564 (TableTree.leaf (56)) (TableTree.leaf (55)))))) (TableTree.node 572 (TableTree.node 568 (TableTree.node 566 (TableTree.leaf (56)) (TableTree.node 567 (TableTree.leaf (58)) (TableTree.leaf (58)))) (TableTree.node 570 (TableTree.node 569 (TableTree.leaf (52)) (TableTree.leaf (52))) (TableTree.node 571 (TableTree.leaf (52)) (TableTree.leaf (53))))) (TableTree.node 576 (TableTree.node 574 (TableTree.node 573 (TableTree.leaf (55)) (TableTree.leaf (56))) (TableTree.node 575 (TableTree.leaf (55)) (TableTree.leaf (56)))) (TableTree.node 578 (TableTree.node 577 (TableTree.leaf (58)) (TableTree.leaf (58))) (TableTree.node 579 (TableTree.leaf (55)) (TableTree.leaf (56))))))))) (TableTree.node 638 (TableTree.node 609 (TableTree.node 594 (TableTree.node 587 (TableTree.node 583 (TableTree.node 581 (TableTree.leaf (57)) (TableTree.node 582 (TableTree.leaf (58)) (TableTree.leaf (59)))) (TableTree.node 585 (TableTree.node 584 (TableTree.leaf (60)) (TableTree.leaf (63))) (TableTree.node 586 (TableTree.leaf (63)) (TableTree.leaf (63))))) (TableTree.node 590 (TableTree.node 588 (TableTree.leaf (63)) (TableTree.node 589 (TableTree.leaf (63)) (TableTree.leaf (63)))) (TableTree.node 592 (TableTree.node 591 (TableTree.leaf (63)) (TableTree.leaf (53))) (TableTree.node 593 (TableTree.leaf (53)) (TableTree.leaf (53)))))) (TableTree.node 601 (TableTree.node 597 (TableTree.node 595 (TableTree.leaf (53)) (TableTree.node 596 (TableTree.leaf (57)) (TableTree.leaf (57)))) (TableTree.node 599 (TableTree.node 598 (TableTree.leaf (59)) (TableTree.leaf (60))) (TableTree.node 600 (TableTree.leaf (59)) (TableTree.leaf (60))))) (TableTree.node 605 (TableTree.node 603 (TableTree.node 602 (TableTree.leaf (57)) (TableTree.leaf (57))) (TableTree.node 604 (TableTree.leaf (59)) (TableTree.leaf (60)))) (TableTree.node 607 (TableTree.node 606 (TableTree.leaf (59)) (TableTree.leaf (60))) (TableTree.node 608 (TableTree.leaf (53)) (TableTree.leaf (53))))))) (TableTree.node 623 (TableTree.node 616 (TableTree.node 612 (TableTree.node 610 (TableTree.leaf (53)) (TableTree.node 611 (TableTree.leaf (53)) (TableTree.leaf (57)))) (TableTree.node 614 (TableTree.node 613 (TableTree.leaf (57)) (TableTree.leaf (59))) (TableTree.node 615 (TableTree.leaf (60)) (TableTree.leaf (59))))) (TableTree.node 619 (TableTree.node 617 (TableTree.leaf (60)) (TableTree.node 618 (TableTree.leaf (57)) (TableTree.leaf (57)))) (TableTree.node 621 (TableTree.node 620 (TableTree.leaf (59)) (TableTree.leaf (60))) (TableTree.node 622 (TableTree.leaf (59)) (TableTree.leaf (60)))))) (TableTree.node 630 (TableTree.node 626 (TableTree.node 624 (TableTree.leaf (53)) (TableTree.node 625 (TableTree.leaf (53)) (TableTree.leaf (53)))) (TableTree.node 628 (TableTree.node 627 (TableTree.leaf (53)) (TableTree.leaf (53))) (TableTree.node 629 (TableTree.leaf (53)) (TableTree.leaf (53))))) (TableTree.node 634 (TableTree.node 632 (TableTree.node 631 (TableTree.leaf (53)) (TableTree.leaf (19))) (TableTree.node 633 (TableTree.leaf (38)) (TableTree.leaf (38)))) (TableTree.node 636 (TableTree.node 635 (TableTree.leaf (19)) (TableTree.leaf (38))) (TableTree.node 637 (TableTree.leaf (19)) (TableTree.leaf (38)))))))) (TableTree.node 667 (TableTree.node 652 (TableTree.node 645 (TableTree.node 641 (TableTree.node 639 (TableTree.leaf (19)) (TableTree.node 640 (TableTree.leaf (38)) (TableTree.leaf (38)))) (TableTree.node 643 (TableTree.node 642 (TableTree.leaf (38)) (TableTree.leaf (64))) (TableTree.node 644 (TableTree.leaf (65)) (TableTree.leaf (64))))) (TableTree.node 648 (TableTree.node 646 (TableTree.leaf (65)) (TableTree.node 647 (TableTree.leaf (67)) (TableTree.leaf (67)))) (TableTree.node 650 (TableTree.node 649 (TableTree.leaf (64)) (TableTree.leaf (65))) (TableTree.node 651 (TableTree.leaf (64)) (TableTree.leaf (65)))))) (TableTree.node 659 (TableTree.node 655 (TableTree.node 653 (TableTree.leaf (67)) (TableTree.node 654 (TableTree.leaf (67)) (TableTree.leaf (69)))) (TableTree.node 657 (TableTree.node 656 (TableTree.leaf (69)) (TableTree.leaf (69))) (TableTree.node 658 (TableTree.leaf (69)) (TableTree.leaf (64))))) (TableTree.node 663 (TableTree.node 661 (TableTree.node 660 (TableTree.leaf (65)) (TableTree.leaf (64))) (TableTree.node 662 (TableTree.leaf (65)) (TableTree.leaf (67)))) (TableTree.node 665 (TableTree.node 664 (TableTree.leaf (67)) (TableTree.leaf (64))) (TableTree.node 666 (TableTree.leaf (65)) (TableTree.leaf (64))))))) (TableTree.node 681 (TableTree.node 674 (TableTree.node 670 (TableTree.node 668 (TableTree.leaf (65)) (TableTree.node 669 (TableTree.leaf (67)) (TableTree.leaf (67)))) (TableTree.node 672 (TableTree.node 671 (TableTree.leaf (69)) (TableTree.leaf (69))) (TableTree.node 673 (TableTree.leaf (69)) (TableTree.leaf (69))))) (TableTree.node 677 (TableTree.node 675 (TableTree.leaf (64)) (TableTree.node 676 (TableTree.leaf (65)) (TableTree.leaf (66)))) (TableTree.node 679 (TableTree.node 678 (TableTree.leaf (67)) (TableTree.leaf (66))) (TableTree.node 680 (TableTree.leaf (66)) (TableTree.leaf (30)))))) (TableTree.node 688 (TableTree.node 684 (TableTree.node 682 (TableTree.leaf (30)) (TableTree.node 683 (TableTree.leaf (69)) (TableTree.leaf (70)))) (TableTree.node 686 (TableTree.node 685 (TableTree.leaf (70)) (TableTree.leaf (70))) (TableTree.node 687 (TableTree.leaf (66)) (TableTree.leaf (66))))) (TableTree.node 692 (TableTree.node 690 (TableTree.node 689 (TableTree.leaf (30)) (TableTree.leaf (66))) (TableTree.node 691 (TableTree.leaf (66)) (TableTree.leaf (30)))) (TableTree.node 694 (TableTree.node 693 (TableTree.leaf (70)) (TableTree.leaf (70))) (TableTree.node 695 (TableTree.leaf (70)) (TableTree.leaf (70)))))))))) (TableTree.node 812 (TableTree.node 754 (TableTree.node 725 (TableTree.node 710 (TableTree.node 703 (TableTree.node 699 (TableTree.node 697 (TableTree.leaf (66)) (TableTree.node 698 (TableTree.leaf (66)) (TableTree.leaf (30)))) (TableTree.node 701 (TableTree.node 700 (TableTree.leaf (30)) (TableTree.leaf (68))) (TableTree.node 702 (TableTree.leaf (68)) (TableTree.leaf (70))))) (TableTree.node 706 (TableTree.node 704 (TableTree.leaf (70)) (TableTree.node 705 (TableTree.leaf (68)) (TableTree.leaf (68)))) (TableTree.node 708 (TableTree.node 707 (TableTree.leaf (68)) (TableTree.leaf (68))) (TableTree.node 709 (TableTree.leaf (68)) (TableTree.leaf (68)))))) (TableTree.node 717 (TableTree.node 713 (TableTree.node 711 (TableTree.leaf (68)) (TableTree.node 712 (TableTree.leaf (41)) (TableTree.leaf (41)))) (TableTree.node 715 (TableTree.node 714 (TableTree.leaf (17)) (TableTree.leaf (17))) (TableTree.node 716 (TableTree.leaf (17)) (TableTree.leaf (17))))) (TableTree.node 721 (TableTree.node 719 (TableTree.node 718 (TableTree.leaf (17)) (TableTree.leaf (17))) (TableTree.node 720 (TableTree.leaf (17)) (TableTree.leaf (17)))) (TableTree.node 723 (TableTree.node 722 (TableTree.leaf (17)) (TableTree.leaf (17))) (TableTree.node 724 (TableTree.leaf (17)) (TableTree.leaf (17))))))) (TableTree.node 739 (TableTree.node 732 (TableTree.node 728 (TableTree.node 726 (TableTree.leaf (17)) (TableTree.node 727 (TableTree.leaf (17)) (TableTree.leaf (42)))) (TableTree.node 730 (TableTree.node 729 (TableTree.leaf (43)) (TableTree.leaf (42))) (TableTree.node 731 (TableTree.leaf (43)) (TableTree.leaf (68))))) (TableTree.node 735 (TableTree.node 733 (TableTree.leaf (68)) (TableTree.node 734 (TableTree.leaf (41)) (TableTree.leaf (41)))) (TableTree.node 737 (TableTree.node 736 (TableTree.leaf (41)) (TableTree.leaf (68))) (TableTree.node 738 (TableTree.leaf (68)) (TableTree.leaf (42)))))) (TableTree.node 746 (TableTree.node 742 (TableTree.node 740 (TableTree.leaf (43)) (TableTree.node 741 (TableTree.leaf (68)) (TableTree.leaf (43)))) (TableTree.node 744 (TableTree.node 743 (TableTree.leaf (43)) (TableTree.leaf (41))) (TableTree.node 745 (TableTree.leaf (43)) (TableTree.leaf (43))))) (TableTree.node 750 (TableTree.node 748 (TableTree.node 747 (TableTree.leaf (41)) (TableTree.leaf (41))) (TableTree.node 749 (TableTree.leaf (41)) (TableTree.leaf (41)))) (TableTree.node 752 (TableTree.node 751 (TableTree.leaf (71)) (TableTree.leaf (71))) (TableTree.node 753 (TableTree.leaf (19)) (TableTree.leaf (38)))))))) (TableTree.node 783 (TableTree.node 768 (TableTree.node 761 (TableTree.node 757 (TableTree.node 755 (TableTree.leaf (19)) (TableTree.node 756 (TableTree.leaf (38)) (TableTree.leaf (71)))) (TableTree.node 759 (TableTree.node 758 (TableTree.leaf (71)) (TableTree.leaf (19))) (TableTree.node 760 (TableTree.leaf (38)) (TableTree.leaf (19))))) (TableTree.node 764 (TableTree.node 762 (TableTree.leaf (38)) (TableTree.node 763 (TableTree.leaf (71)) (TableTree.leaf (71)))) (TableTree.node 766 (TableTree.node 765 (TableTree.leaf (19)) (TableTree.leaf (38))) (TableTree.node 767 (TableTree.leaf (19)) (TableTree.leaf (38)))))) (TableTree.node 775 (TableTree.node 771 (TableTree.node 769 (TableTree.leaf (71)) (TableTree.node 770 (TableTree.leaf (71)) (TableTree.leaf (71)))) (TableTree.node 773 (TableTree.node 772 (TableTree.leaf (43)) (TableTree.leaf (43))) (TableTree.node 774 (TableTree.leaf (71)) (TableTree.leaf (71))))) (TableTree.node 779 (TableTree.node 777 (TableTree.node 776 (TableTree.leaf (71)) (TableTree.leaf (17))) (TableTree.node 778 (TableTree.leaf (17)) (TableTree.leaf (71)))) (TableTree.node 781 (TableTree.node 780 (TableTree.leaf (71)) (TableTree.leaf (71))) (TableTree.node 782 (TableTree.leaf (41)) (TableTree.leaf (41))))))) (TableTree.node 797 (TableTree.node 790 (TableTree.node 786 (TableTree.node 784 (TableTree.leaf (17)) (TableTree.node 785 (TableTree.leaf (42)) (TableTree.leaf (43)))) (TableTree.node 788 (TableTree.node 787 (TableTree.leaf (42)) (TableTree.leaf (43))) (TableTree.node 789 (TableTree.leaf (68)) (TableTree.leaf (68))))) (TableTree.node 793 (TableTree.node 791 (TableTree.leaf (42)) (TableTree.node 792 (TableTree.leaf (42)) (TableTree.leaf (43)))) (TableTree.node 795 (TableTree.node 794 (TableTree.leaf (68)) (TableTree.leaf (68))) (TableTree.node 796 (TableTree.leaf (68)) (TableTree.leaf (68)))))) (TableTree.node 804 (TableTree.node 800 (TableTree.node 798 (TableTree.leaf (68)) (TableTree.node 799 (TableTree.leaf (41)) (TableTree.leaf (68)))) (TableTree.node 802 (TableTree.node 801 (TableTree.leaf (68)) (TableTree.leaf (68))) (TableTree.node 803 (TableTree.leaf (42)) (TableTree.leaf (43))))) (TableTree.node 808 (TableTree.node 806 (TableTree.node 805 (TableTree.leaf (43)) (TableTree.leaf (68))) (TableTree.node 807 (TableTree.leaf (43)) (TableTree.leaf (43)))) (TableTree.node 810 (TableTree.node 809 (TableTree.leaf (41)) (TableTree.leaf (68))) (TableTree.node 811 (TableTree.leaf (68)) (TableTree.leaf (68))))))))) (TableTree.node 870 (TableTree.node 841 (TableTree.node 826 (TableTree.node 819 (TableTree.node 815 (TableTree.node 813 (TableTree.leaf (72)) (TableTree.node 814 (TableTree.leaf (72)) (TableTree.leaf (72)))) (TableTree.node 817 (TableTree.node 816 (TableTree.leaf (72)) (TableTree.leaf (72))) (TableTree.node 818 (TableTree.leaf (72)) (TableTree.leaf (72))))) (TableTree.node 822 (TableTree.node 820 (TableTree.leaf (72)) (TableTree.node 821 (TableTree.leaf (72)) (TableTree.leaf (42)))) (TableTree.node 824 (TableTree.node 823 (TableTree.leaf (43)) (TableTree.leaf (44))) (TableTree.node 825 (TableTree.leaf (44)) (TableTree.leaf (41)))))) (TableTree.node 833 (TableTree.node 829 (TableTree.node 827 (TableTree.leaf (41)) (TableTree.node 828 (TableTree.leaf (42)) (TableTree.leaf (43)))) (TableTree.node 831 (TableTree.node 830 (TableTree.leaf (42)) (TableTree.leaf (43))) (TableTree.node 832 (TableTree.leaf (44)) (TableTree.leaf (44))))) (TableTree.node 837 (TableTree.node 835 (TableTree.node 834 (TableTree.leaf (42)) (TableTree.leaf (43))) (TableTree.node 836 (TableTree.leaf (42)) (TableTree.leaf (43)))) (TableTree.node 839 (TableTree.node 838 (TableTree.leaf (44)) (TableTree.leaf (44))) (TableTree.node 840 (TableTree.leaf (41)) (TableTree.leaf (42))))))) (TableTree.node 855 (TableTree.node 848 (TableTree.node 844 (TableTree.node 842 (TableTree.leaf (43)) (TableTree.node 843 (TableTree.leaf (42)) (TableTree.leaf (43)))) (TableTree.node 846 (TableTree.node 845 (TableTree.leaf (44)) (TableTree.leaf (44))) (TableTree.node 847 (TableTree.leaf (42)) (TableTree.leaf (43))))) (TableTree.node 851 (TableTree.node 849 (TableTree.leaf (44)) (TableTree.node 850 (TableTree.leaf (41)) (TableTree.leaf (41)))) (TableTree.node 853 (TableTree.node 852 (TableTree.leaf (43)) (TableTree.leaf (43))) (TableTree.node 854 (TableTree.leaf (42)) (TableTree.leaf (42)))))) (TableTree.node 862 (TableTree.node 858 (TableTree.node 856 (TableTree.leaf (43)) (TableTree.node 857 (TableTree.leaf (43)) (TableTree.leaf (42)))) (TableTree.node 860 (TableTree.node 859 (TableTree.leaf (42)) (TableTree.leaf (43))) (TableTree.node 861 (TableTree.leaf (43)) (TableTree.leaf (41))))) (TableTree.node 866 (TableTree.node 864 (TableTree.node 863 (TableTree.leaf (41)) (TableTree.leaf (41))) (TableTree.node 865 (TableTree.leaf (41)) (TableTree.leaf (68)))) (TableTree.node 868 (TableTree.node 867 (TableTree.leaf (68)) (TableTree.leaf (68))) (TableTree.node 869 (TableTree.leaf (68)) (TableTree.leaf (41)))))))) (TableTree.node 899 (TableTree.node 884 (TableTree.node 877 (TableTree.node 873 (TableTree.node 871 (TableTree.leaf (41)) (TableTree.node 872 (TableTree.leaf (41)) (TableTree.leaf (68)))) (TableTree.node 875 (TableTree.node 874 (TableTree.leaf (68)) (TableTree.leaf (68))) (TableTree.node 876 (TableTree.leaf (43)) (TableTree.leaf (41))))) (TableTree.node 880 (TableTree.node 878 (TableTree.leaf (43)) (TableTree.node 879 (TableTree.leaf (43)) (TableTree.leaf (41)))) (TableTree.node 882 (TableTree.node 881 (TableTree.leaf (41)) (TableTree.leaf (68))) (TableTree.node 883 (TableTree.leaf (68)) (TableTree.leaf (68)))))) (TableTree.node 891 (TableTree.node 887 (TableTree.node 885 (TableTree.leaf (68)) (TableTree.node 886 (TableTree.leaf (41)) (TableTree.leaf (41)))) (TableTree.node 889 (TableTree.node 888 (TableTree.leaf (41)) (TableTree.leaf (41))) (TableTree.node 890 (TableTree.leaf (41)) (TableTree.leaf (41))))) (TableTree.node 895 (TableTree.node 893 (TableTree.node 892 (TableTree.leaf (41)) (TableTree.leaf (41))) (TableTree.node 894 (TableTree.leaf (41)) (TableTree.leaf (42)))) (TableTree.node 897 (TableTree.node 896 (TableTree.leaf (42)) (TableTree.leaf (42))) (TableTree.node 898 (TableTree.leaf (42)) (TableTree.leaf (42))))))) (TableTree.node 914 (TableTree.node 906 (TableTree.node 902 (TableTree.node 900 (TableTree.leaf (42)) (TableTree.node 901 (TableTree.leaf (42)) (TableTree.leaf (42)))) (TableTree.node 904 (TableTree.node 903 (TableTree.leaf (42)) (TableTree.leaf (43))) (TableTree.node 905 (TableTree.leaf (43)) (TableTree.leaf (43))))) (TableTree.node 910 (TableTree.node 908 (TableTree.node 907 (TableTree.leaf (43)) (TableTree.leaf (43))) (TableTree.node 909 (TableTree.leaf (43)) (TableTree.leaf (43)))) (TableTree.node 912 (TableTree.node 911 (TableTree.leaf (43)) (TableTree.leaf (43))) (TableTree.node 913 (TableTree.leaf (44)) (TableTree.leaf (44)))))) (TableTree.node 921 (TableTree.node 917 (TableTree.node 915 (TableTree.leaf (44)) (TableTree.node 916 (TableTree.leaf (44)) (TableTree.leaf (44)))) (TableTree.node 919 (TableTree.node 918 (TableTree.leaf (44)) (TableTree.leaf (44))) (TableTree.node 920 (TableTree.leaf (44)) (TableTree.leaf (44))))) (TableTree.node 925 (TableTree.node 923 (TableTree.node 922 (TableTree.leaf (68)) (TableTree.leaf (68))) (TableTree.node 924 (TableTree.leaf (68)) (TableTree.leaf (68)))) (TableTree.node 927 (TableTree.node 926 (TableTree.leaf (68)) (TableTree.leaf (68))) (TableTree.node 928 (TableTree.leaf (68)) (TableTree.leaf (68))))))))))))
private def sourceAt (i : ℕ) : ℕ := if i < 929 then TableTree.lookup sourceAtTree i else 0
private def carryAtTree : TableTree (ℕ) := (TableTree.node 464 (TableTree.node 232 (TableTree.node 116 (TableTree.node 58 (TableTree.node 29 (TableTree.node 14 (TableTree.node 7 (TableTree.node 3 (TableTree.node 1 (TableTree.leaf (0)) (TableTree.node 2 (TableTree.leaf (1)) (TableTree.leaf (2)))) (TableTree.node 5 (TableTree.node 4 (TableTree.leaf (3)) (TableTree.leaf (4))) (TableTree.node 6 (TableTree.leaf (5)) (TableTree.leaf (6))))) (TableTree.node 10 (TableTree.node 8 (TableTree.leaf (7)) (TableTree.node 9 (TableTree.leaf (8)) (TableTree.leaf (0)))) (TableTree.node 12 (TableTree.node 11 (TableTree.leaf (1)) (TableTree.leaf (2))) (TableTree.node 13 (TableTree.leaf (3)) (TableTree.leaf (4)))))) (TableTree.node 21 (TableTree.node 17 (TableTree.node 15 (TableTree.leaf (5)) (TableTree.node 16 (TableTree.leaf (6)) (TableTree.leaf (7)))) (TableTree.node 19 (TableTree.node 18 (TableTree.leaf (8)) (TableTree.leaf (0))) (TableTree.node 20 (TableTree.leaf (1)) (TableTree.leaf (2))))) (TableTree.node 25 (TableTree.node 23 (TableTree.node 22 (TableTree.leaf (3)) (TableTree.leaf (4))) (TableTree.node 24 (TableTree.leaf (5)) (TableTree.leaf (6)))) (TableTree.node 27 (TableTree.node 26 (TableTree.leaf (7)) (TableTree.leaf (8))) (TableTree.node 28 (TableTree.leaf (0)) (TableTree.leaf (0))))))) (TableTree.node 43 (TableTree.node 36 (TableTree.node 32 (TableTree.node 30 (TableTree.leaf (1)) (TableTree.node 31 (TableTree.leaf (1)) (TableTree.leaf (2)))) (TableTree.node 34 (TableTree.node 33 (TableTree.leaf (2)) (TableTree.leaf (3))) (TableTree.node 35 (TableTree.leaf (3)) (TableTree.leaf (4))))) (TableTree.node 39 (TableTree.node 37 (TableTree.leaf (4)) (TableTree.node 38 (TableTree.leaf (5)) (TableTree.leaf (5)))) (TableTree.node 41 (TableTree.node 40 (TableTree.leaf (6)) (TableTree.leaf (6))) (TableTree.node 42 (TableTree.leaf (7)) (TableTree.leaf (7)))))) (TableTree.node 50 (TableTree.node 46 (TableTree.node 44 (TableTree.leaf (8)) (TableTree.node 45 (TableTree.leaf (8)) (TableTree.leaf (0)))) (TableTree.node 48 (TableTree.node 47 (TableTree.leaf (1)) (TableTree.leaf (2))) (TableTree.node 49 (TableTree.leaf (3)) (TableTree.leaf (4))))) (TableTree.node 54 (TableTree.node 52 (TableTree.node 51 (TableTree.leaf (5)) (TableTree.leaf (6))) (TableTree.node 53 (TableTree.leaf (7)) (TableTree.leaf (8)))) (TableTree.node 56 (TableTree.node 55 (TableTree.leaf (0)) (TableTree.leaf (0))) (TableTree.node 57 (TableTree.leaf (1)) (TableTree.leaf (1)))))))) (TableTree.node 87 (TableTree.node 72 (TableTree.node 65 (TableTree.node 61 (TableTree.node 59 (TableTree.leaf (2)) (TableTree.node 60 (TableTree.leaf (2)) (TableTree.leaf (3)))) (TableTree.node 63 (TableTree.node 62 (TableTree.leaf (3)) (TableTree.leaf (4))) (TableTree.node 64 (TableTree.leaf (4)) (TableTree.leaf (5))))) (TableTree.node 68 (TableTree.node 66 (TableTree.leaf (5)) (TableTree.node 67 (TableTree.leaf (6)) (TableTree.leaf (6)))) (TableTree.node 70 (TableTree.node 69 (TableTree.leaf (7)) (TableTree.leaf (7))) (TableTree.node 71 (TableTree.leaf (8)) (TableTree.leaf (8)))))) (TableTree.node 79 (TableTree.node 75 (TableTree.node 73 (TableTree.leaf (0)) (TableTree.node 74 (TableTree.leaf (1)) (TableTree.leaf (0)))) (TableTree.node 77 (TableTree.node 76 (TableTree.leaf (1)) (TableTree.leaf (2))) (TableTree.node 78 (TableTree.leaf (3)) (TableTree.leaf (2))))) (TableTree.node 83 (TableTree.node 81 (TableTree.node 80 (TableTree.leaf (3)) (TableTree.leaf (4))) (TableTree.node 82 (TableTree.leaf (5)) (TableTree.leaf (4)))) (TableTree.node 85 (TableTree.node 84 (TableTree.leaf (5)) (TableTree.leaf (6))) (TableTree.node 86 (TableTree.leaf (7)) (TableTree.leaf (6))))))) (TableTree.node 101 (TableTree.node 94 (TableTree.node 90 (TableTree.node 88 (TableTree.leaf (7)) (TableTree.node 89 (TableTree.leaf (8)) (TableTree.leaf (0)))) (TableTree.node 92 (TableTree.node 91 (TableTree.leaf (0)) (TableTree.leaf (8))) (TableTree.node 93 (TableTree.leaf (0)) (TableTree.leaf (1))))) (TableTree.node 97 (TableTree.node 95 (TableTree.leaf (1)) (TableTree.node 96 (TableTree.leaf (2)) (TableTree.leaf (2)))) (TableTree.node 99 (TableTree.node 98 (TableTree.leaf (1)) (TableTree.leaf (2))) (TableTree.node 100 (TableTree.leaf (3)) (TableTree.leaf (3)))))) (TableTree.node 108 (TableTree.node 104 (TableTree.node 102 (TableTree.leaf (4)) (TableTree.node 103 (TableTree.leaf (4)) (TableTree.leaf (3)))) (TableTree.node 106 (TableTree.node 105 (TableTree.leaf (4)) (TableTree.leaf (5))) (TableTree.node 107 (TableTree.leaf (5)) (TableTree.leaf (6))))) (TableTree.node 112 (TableTree.node 110 (TableTree.node 109 (TableTree.leaf (6)) (TableTree.leaf (5))) (TableTree.node 111 (TableTree.leaf (6)) (TableTree.leaf (7)))) (TableTree.node 114 (TableTree.node 113 (TableTree.leaf (7)) (TableTree.leaf (8))) (TableTree.node 115 (TableTree.leaf (8)) (TableTree.leaf (7))))))))) (TableTree.node 174 (TableTree.node 145 (TableTree.node 130 (TableTree.node 123 (TableTree.node 119 (TableTree.node 117 (TableTree.leaf (8)) (TableTree.node 118 (TableTree.leaf (0)) (TableTree.leaf (1)))) (TableTree.node 121 (TableTree.node 120 (TableTree.leaf (2)) (TableTree.leaf (3))) (TableTree.node 122 (TableTree.leaf (4)) (TableTree.leaf (5))))) (TableTree.node 126 (TableTree.node 124 (TableTree.leaf (6)) (TableTree.node 125 (TableTree.leaf (7)) (TableTree.leaf (8)))) (TableTree.node 128 (TableTree.node 127 (TableTree.leaf (0)) (TableTree.leaf (0))) (TableTree.node 129 (TableTree.leaf (1)) (TableTree.leaf (1)))))) (TableTree.node 137 (TableTree.node 133 (TableTree.node 131 (TableTree.leaf (2)) (TableTree.node 132 (TableTree.leaf (2)) (TableTree.leaf (3)))) (TableTree.node 135 (TableTree.node 134 (TableTree.leaf (3)) (TableTree.leaf (4))) (TableTree.node 136 (TableTree.leaf (4)) (TableTree.leaf (5))))) (TableTree.node 141 (TableTree.node 139 (TableTree.node 138 (TableTree.leaf (5)) (TableTree.leaf (6))) (TableTree.node 140 (TableTree.leaf (6)) (TableTree.leaf (7)))) (TableTree.node 143 (TableTree.node 142 (TableTree.leaf (7)) (TableTree.leaf (8))) (TableTree.node 144 (TableTree.leaf (8)) (TableTree.leaf (0))))))) (TableTree.node 159 (TableTree.node 152 (TableTree.node 148 (TableTree.node 146 (TableTree.leaf (1)) (TableTree.node 147 (TableTree.leaf (0)) (TableTree.leaf (1)))) (TableTree.node 150 (TableTree.node 149 (TableTree.leaf (2)) (TableTree.leaf (3))) (TableTree.node 151 (TableTree.leaf (2)) (TableTree.leaf (3))))) (TableTree.node 155 (TableTree.node 153 (TableTree.leaf (4)) (TableTree.node 154 (TableTree.leaf (5)) (TableTree.leaf (4)))) (TableTree.node 157 (TableTree.node 156 (TableTree.leaf (5)) (TableTree.leaf (6))) (TableTree.node 158 (TableTree.leaf (7)) (TableTree.leaf (6)))))) (TableTree.node 166 (TableTree.node 162 (TableTree.node 160 (TableTree.leaf (7)) (TableTree.node 161 (TableTree.leaf (8)) (TableTree.leaf (0)))) (TableTree.node 164 (TableTree.node 163 (TableTree.leaf (8)) (TableTree.leaf (0))) (TableTree.node 165 (TableTree.leaf (0)) (TableTree.leaf (1))))) (TableTree.node 170 (TableTree.node 168 (TableTree.node 167 (TableTree.leaf (2)) (TableTree.leaf (1))) (TableTree.node 169 (TableTree.leaf (1)) (TableTree.leaf (2)))) (TableTree.node 172 (TableTree.node 171 (TableTree.leaf (2)) (TableTree.leaf (3))) (TableTree.node 173 (TableTree.leaf (4)) (TableTree.leaf (3)))))))) (TableTree.node 203 (TableTree.node 188 (TableTree.node 181 (TableTree.node 177 (TableTree.node 175 (TableTree.leaf (3)) (TableTree.node 176 (TableTree.leaf (4)) (TableTree.leaf (4)))) (TableTree.node 179 (TableTree.node 178 (TableTree.leaf (5)) (TableTree.leaf (6))) (TableTree.node 180 (TableTree.leaf (5)) (TableTree.leaf (5))))) (TableTree.node 184 (TableTree.node 182 (TableTree.leaf (6)) (TableTree.node 183 (TableTree.leaf (6)) (TableTree.leaf (7)))) (TableTree.node 186 (TableTree.node 185 (TableTree.leaf (8)) (TableTree.leaf (7))) (TableTree.node 187 (TableTree.leaf (7)) (TableTree.leaf (8)))))) (TableTree.node 195 (TableTree.node 191 (TableTree.node 189 (TableTree.leaf (8)) (TableTree.node 190 (TableTree.leaf (0)) (TableTree.leaf (1)))) (TableTree.node 193 (TableTree.node 192 (TableTree.leaf (2)) (TableTree.leaf (3))) (TableTree.node 194 (TableTree.leaf (0)) (TableTree.leaf (1))))) (TableTree.node 199 (TableTree.node 197 (TableTree.node 196 (TableTree.leaf (2)) (TableTree.leaf (3))) (TableTree.node 198 (TableTree.leaf (4)) (TableTree.leaf (5)))) (TableTree.node 201 (TableTree.node 200 (TableTree.leaf (6)) (TableTree.leaf (7))) (TableTree.node 202 (TableTree.leaf (4)) (TableTree.leaf (5))))))) (TableTree.node 217 (TableTree.node 210 (TableTree.node 206 (TableTree.node 204 (TableTree.leaf (6)) (TableTree.node 205 (TableTree.leaf (7)) (TableTree.leaf (8)))) (TableTree.node 208 (TableTree.node 207 (TableTree.leaf (0)) (TableTree.leaf (0))) (TableTree.node 209 (TableTree.leaf (1)) (TableTree.leaf (1))))) (TableTree.node 213 (TableTree.node 211 (TableTree.leaf (2)) (TableTree.node 212 (TableTree.leaf (2)) (TableTree.leaf (8)))) (TableTree.node 215 (TableTree.node 214 (TableTree.leaf (0)) (TableTree.leaf (1))) (TableTree.node 216 (TableTree.leaf (2)) (TableTree.leaf (3)))))) (TableTree.node 224 (TableTree.node 220 (TableTree.node 218 (TableTree.leaf (3)) (TableTree.node 219 (TableTree.leaf (4)) (TableTree.leaf (4)))) (TableTree.node 222 (TableTree.node 221 (TableTree.leaf (5)) (TableTree.leaf (5))) (TableTree.node 223 (TableTree.leaf (6)) (TableTree.leaf (6))))) (TableTree.node 228 (TableTree.node 226 (TableTree.node 225 (TableTree.leaf (3)) (TableTree.leaf (4))) (TableTree.node 227 (TableTree.leaf (5)) (TableTree.leaf (6)))) (TableTree.node 230 (TableTree.node 229 (TableTree.leaf (7)) (TableTree.leaf (7))) (TableTree.node 231 (TableTree.leaf (8)) (TableTree.leaf (8)))))))))) (TableTree.node 348 (TableTree.node 290 (TableTree.node 261 (TableTree.node 246 (TableTree.node 239 (TableTree.node 235 (TableTree.node 233 (TableTree.leaf (0)) (TableTree.node 234 (TableTree.leaf (0)) (TableTree.leaf (1)))) (TableTree.node 237 (TableTree.node 236 (TableTree.leaf (1)) (TableTree.leaf (0))) (TableTree.node 238 (TableTree.leaf (1)) (TableTree.leaf (7))))) (TableTree.node 242 (TableTree.node 240 (TableTree.leaf (8)) (TableTree.node 241 (TableTree.leaf (0)) (TableTree.leaf (1)))) (TableTree.node 244 (TableTree.node 243 (TableTree.leaf (2)) (TableTree.leaf (2))) (TableTree.node 245 (TableTree.leaf (3)) (TableTree.leaf (3)))))) (TableTree.node 253 (TableTree.node 249 (TableTree.node 247 (TableTree.leaf (2)) (TableTree.node 248 (TableTree.leaf (3)) (TableTree.leaf (4)))) (TableTree.node 251 (TableTree.node 250 (TableTree.leaf (4)) (TableTree.leaf (5))) (TableTree.node 252 (TableTree.leaf (5)) (TableTree.leaf (4))))) (TableTree.node 257 (TableTree.node 255 (TableTree.node 254 (TableTree.leaf (5)) (TableTree.leaf (2))) (TableTree.node 256 (TableTree.leaf (3)) (TableTree.leaf (4)))) (TableTree.node 259 (TableTree.node 258 (TableTree.leaf (5)) (TableTree.leaf (6))) (TableTree.node 260 (TableTree.leaf (6)) (TableTree.leaf (7))))))) (TableTree.node 275 (TableTree.node 268 (TableTree.node 264 (TableTree.node 262 (TableTree.leaf (7)) (TableTree.node 263 (TableTree.leaf (6)) (TableTree.leaf (7)))) (TableTree.node 266 (TableTree.node 265 (TableTree.leaf (8)) (TableTree.leaf (8))) (TableTree.node 267 (TableTree.leaf (0)) (TableTree.leaf (8))))) (TableTree.node 271 (TableTree.node 269 (TableTree.leaf (0)) (TableTree.node 270 (TableTree.leaf (0)) (TableTree.leaf (6)))) (TableTree.node 273 (TableTree.node 272 (TableTree.leaf (7)) (TableTree.leaf (8))) (TableTree.node 274 (TableTree.leaf (0)) (TableTree.leaf (1)))))) (TableTree.node 282 (TableTree.node 278 (TableTree.node 276 (TableTree.leaf (2)) (TableTree.node 277 (TableTree.leaf (1)) (TableTree.leaf (1)))) (TableTree.node 280 (TableTree.node 279 (TableTree.leaf (2)) (TableTree.leaf (2))) (TableTree.node 281 (TableTree.leaf (3)) (TableTree.leaf (4))))) (TableTree.node 286 (TableTree.node 284 (TableTree.node 283 (TableTree.leaf (3)) (TableTree.leaf (3))) (TableTree.node 285 (TableTree.leaf (4)) (TableTree.leaf (4)))) (TableTree.node 288 (TableTree.node 287 (TableTree.leaf (1)) (TableTree.leaf (2))) (TableTree.node 289 (TableTree.leaf (3)) (TableTree.leaf (4)))))))) (TableTree.node 319 (TableTree.node 304 (TableTree.node 297 (TableTree.node 293 (TableTree.node 291 (TableTree.leaf (5)) (TableTree.node 292 (TableTree.leaf (6)) (TableTree.leaf (5)))) (TableTree.node 295 (TableTree.node 294 (TableTree.leaf (5)) (TableTree.leaf (6))) (TableTree.node 296 (TableTree.leaf (6)) (TableTree.leaf (7))))) (TableTree.node 300 (TableTree.node 298 (TableTree.leaf (8)) (TableTree.node 299 (TableTree.leaf (7)) (TableTree.leaf (7)))) (TableTree.node 302 (TableTree.node 301 (TableTree.leaf (8)) (TableTree.leaf (8))) (TableTree.node 303 (TableTree.leaf (5)) (TableTree.leaf (6)))))) (TableTree.node 311 (TableTree.node 307 (TableTree.node 305 (TableTree.leaf (7)) (TableTree.node 306 (TableTree.leaf (8)) (TableTree.leaf (0)))) (TableTree.node 309 (TableTree.node 308 (TableTree.leaf (0)) (TableTree.leaf (1))) (TableTree.node 310 (TableTree.leaf (1)) (TableTree.leaf (2))))) (TableTree.node 315 (TableTree.node 313 (TableTree.node 312 (TableTree.leaf (2)) (TableTree.leaf (3))) (TableTree.node 314 (TableTree.leaf (3)) (TableTree.leaf (4)))) (TableTree.node 317 (TableTree.node 316 (TableTree.leaf (4)) (TableTree.leaf (5))) (TableTree.node 318 (TableTree.leaf (5)) (TableTree.leaf (6))))))) (TableTree.node 333 (TableTree.node 326 (TableTree.node 322 (TableTree.node 320 (TableTree.leaf (6)) (TableTree.node 321 (TableTree.leaf (7)) (TableTree.leaf (7)))) (TableTree.node 324 (TableTree.node 323 (TableTree.leaf (8)) (TableTree.leaf (8))) (TableTree.node 325 (TableTree.leaf (0)) (TableTree.leaf (0))))) (TableTree.node 329 (TableTree.node 327 (TableTree.leaf (1)) (TableTree.node 328 (TableTree.leaf (1)) (TableTree.leaf (0)))) (TableTree.node 331 (TableTree.node 330 (TableTree.leaf (1)) (TableTree.leaf (2))) (TableTree.node 332 (TableTree.leaf (2)) (TableTree.leaf (3)))))) (TableTree.node 340 (TableTree.node 336 (TableTree.node 334 (TableTree.leaf (3)) (TableTree.node 335 (TableTree.leaf (2)) (TableTree.leaf (3)))) (TableTree.node 338 (TableTree.node 337 (TableTree.leaf (4)) (TableTree.leaf (4))) (TableTree.node 339 (TableTree.leaf (5)) (TableTree.leaf (5))))) (TableTree.node 344 (TableTree.node 342 (TableTree.node 341 (TableTree.leaf (4)) (TableTree.leaf (5))) (TableTree.node 343 (TableTree.leaf (6)) (TableTree.leaf (6)))) (TableTree.node 346 (TableTree.node 345 (TableTree.leaf (7)) (TableTree.leaf (7))) (TableTree.node 347 (TableTree.leaf (6)) (TableTree.leaf (7))))))))) (TableTree.node 406 (TableTree.node 377 (TableTree.node 362 (TableTree.node 355 (TableTree.node 351 (TableTree.node 349 (TableTree.leaf (8)) (TableTree.node 350 (TableTree.leaf (8)) (TableTree.leaf (0)))) (TableTree.node 353 (TableTree.node 352 (TableTree.leaf (8)) (TableTree.leaf (1))) (TableTree.node 354 (TableTree.leaf (2)) (TableTree.leaf (3))))) (TableTree.node 358 (TableTree.node 356 (TableTree.leaf (4)) (TableTree.node 357 (TableTree.leaf (5)) (TableTree.leaf (6)))) (TableTree.node 360 (TableTree.node 359 (TableTree.leaf (7)) (TableTree.leaf (8))) (TableTree.node 361 (TableTree.leaf (0)) (TableTree.leaf (1)))))) (TableTree.node 369 (TableTree.node 365 (TableTree.node 363 (TableTree.leaf (2)) (TableTree.node 364 (TableTree.leaf (3)) (TableTree.leaf (4)))) (TableTree.node 367 (TableTree.node 366 (TableTree.leaf (5)) (TableTree.leaf (6))) (TableTree.node 368 (TableTree.leaf (7)) (TableTree.leaf (8))))) (TableTree.node 373 (TableTree.node 371 (TableTree.node 370 (TableTree.leaf (0)) (TableTree.leaf (1))) (TableTree.node 372 (TableTree.leaf (2)) (TableTree.leaf (3)))) (TableTree.node 375 (TableTree.node 374 (TableTree.leaf (5)) (TableTree.leaf (8))) (TableTree.node 376 (TableTree.leaf (0)) (TableTree.leaf (1))))))) (TableTree.node 391 (TableTree.node 384 (TableTree.node 380 (TableTree.node 378 (TableTree.leaf (0)) (TableTree.node 379 (TableTree.leaf (0)) (TableTree.leaf (1)))) (TableTree.node 382 (TableTree.node 381 (TableTree.leaf (1)) (TableTree.leaf (0))) (TableTree.node 383 (TableTree.leaf (1)) (TableTree.leaf (2))))) (TableTree.node 387 (TableTree.node 385 (TableTree.leaf (3)) (TableTree.node 386 (TableTree.leaf (4)) (TableTree.leaf (5)))) (TableTree.node 389 (TableTree.node 388 (TableTree.leaf (2)) (TableTree.leaf (2))) (TableTree.node 390 (TableTree.leaf (3)) (TableTree.leaf (3)))))) (TableTree.node 398 (TableTree.node 394 (TableTree.node 392 (TableTree.leaf (2)) (TableTree.node 393 (TableTree.leaf (3)) (TableTree.leaf (4)))) (TableTree.node 396 (TableTree.node 395 (TableTree.leaf (4)) (TableTree.leaf (5))) (TableTree.node 397 (TableTree.leaf (5)) (TableTree.leaf (4))))) (TableTree.node 402 (TableTree.node 400 (TableTree.node 399 (TableTree.leaf (5)) (TableTree.leaf (6))) (TableTree.node 401 (TableTree.leaf (7)) (TableTree.leaf (8)))) (TableTree.node 404 (TableTree.node 403 (TableTree.leaf (0)) (TableTree.leaf (6))) (TableTree.node 405 (TableTree.leaf (6)) (TableTree.leaf (7)))))))) (TableTree.node 435 (TableTree.node 420 (TableTree.node 413 (TableTree.node 409 (TableTree.node 407 (TableTree.leaf (7)) (TableTree.node 408 (TableTree.leaf (6)) (TableTree.leaf (7)))) (TableTree.node 411 (TableTree.node 410 (TableTree.leaf (8)) (TableTree.leaf (8))) (TableTree.node 412 (TableTree.leaf (8)) (TableTree.leaf (1))))) (TableTree.node 416 (TableTree.node 414 (TableTree.leaf (2)) (TableTree.node 415 (TableTree.leaf (1)) (TableTree.leaf (2)))) (TableTree.node 418 (TableTree.node 417 (TableTree.leaf (1)) (TableTree.leaf (4))) (TableTree.node 419 (TableTree.leaf (3)) (TableTree.leaf (5)))))) (TableTree.node 427 (TableTree.node 423 (TableTree.node 421 (TableTree.leaf (6)) (TableTree.node 422 (TableTree.leaf (7)) (TableTree.leaf (8)))) (TableTree.node 425 (TableTree.node 424 (TableTree.leaf (5)) (TableTree.leaf (6))) (TableTree.node 426 (TableTree.leaf (5)) (TableTree.leaf (6))))) (TableTree.node 431 (TableTree.node 429 (TableTree.node 428 (TableTree.leaf (7)) (TableTree.leaf (8))) (TableTree.node 430 (TableTree.leaf (0)) (TableTree.leaf (1)))) (TableTree.node 433 (TableTree.node 432 (TableTree.leaf (2)) (TableTree.leaf (3))) (TableTree.node 434 (TableTree.leaf (4)) (TableTree.leaf (5))))))) (TableTree.node 449 (TableTree.node 442 (TableTree.node 438 (TableTree.node 436 (TableTree.leaf (7)) (TableTree.node 437 (TableTree.leaf (8)) (TableTree.leaf (2)))) (TableTree.node 440 (TableTree.node 439 (TableTree.leaf (2)) (TableTree.leaf (0))) (TableTree.node 441 (TableTree.leaf (0)) (TableTree.leaf (0))))) (TableTree.node 445 (TableTree.node 443 (TableTree.leaf (1)) (TableTree.node 444 (TableTree.leaf (2)) (TableTree.leaf (1)))) (TableTree.node 447 (TableTree.node 446 (TableTree.leaf (1)) (TableTree.leaf (2))) (TableTree.node 448 (TableTree.leaf (2)) (TableTree.leaf (3)))))) (TableTree.node 456 (TableTree.node 452 (TableTree.node 450 (TableTree.leaf (4)) (TableTree.node 451 (TableTree.leaf (3)) (TableTree.leaf (3)))) (TableTree.node 454 (TableTree.node 453 (TableTree.leaf (4)) (TableTree.leaf (4))) (TableTree.node 455 (TableTree.leaf (6)) (TableTree.leaf (7))))) (TableTree.node 460 (TableTree.node 458 (TableTree.node 457 (TableTree.leaf (0)) (TableTree.leaf (1))) (TableTree.node 459 (TableTree.leaf (2)) (TableTree.leaf (3)))) (TableTree.node 462 (TableTree.node 461 (TableTree.leaf (4)) (TableTree.leaf (5))) (TableTree.node 463 (TableTree.leaf (6)) (TableTree.leaf (5))))))))))) (TableTree.node 696 (TableTree.node 580 (TableTree.node 522 (TableTree.node 493 (TableTree.node 478 (TableTree.node 471 (TableTree.node 467 (TableTree.node 465 (TableTree.leaf (5)) (TableTree.node 466 (TableTree.leaf (6)) (TableTree.leaf (6)))) (TableTree.node 469 (TableTree.node 468 (TableTree.leaf (7)) (TableTree.leaf (8))) (TableTree.node 470 (TableTree.leaf (7)) (TableTree.leaf (7))))) (TableTree.node 474 (TableTree.node 472 (TableTree.leaf (8)) (TableTree.node 473 (TableTree.leaf (8)) (TableTree.leaf (0)))) (TableTree.node 476 (TableTree.node 475 (TableTree.leaf (0)) (TableTree.leaf (1))) (TableTree.node 477 (TableTree.leaf (1)) (TableTree.leaf (0)))))) (TableTree.node 485 (TableTree.node 481 (TableTree.node 479 (TableTree.leaf (1)) (TableTree.node 480 (TableTree.leaf (2)) (TableTree.leaf (2)))) (TableTree.node 483 (TableTree.node 482 (TableTree.leaf (3)) (TableTree.leaf (3))) (TableTree.node 484 (TableTree.leaf (2)) (TableTree.leaf (3))))) (TableTree.node 489 (TableTree.node 487 (TableTree.node 486 (TableTree.leaf (0)) (TableTree.leaf (1))) (TableTree.node 488 (TableTree.leaf (2)) (TableTree.leaf (3)))) (TableTree.node 491 (TableTree.node 490 (TableTree.leaf (5)) (TableTree.leaf (6))) (TableTree.node 492 (TableTree.leaf (7)) (TableTree.leaf (8))))))) (TableTree.node 507 (TableTree.node 500 (TableTree.node 496 (TableTree.node 494 (TableTree.leaf (0)) (TableTree.node 495 (TableTree.leaf (1)) (TableTree.leaf (2)))) (TableTree.node 498 (TableTree.node 497 (TableTree.leaf (3)) (TableTree.leaf (4))) (TableTree.node 499 (TableTree.leaf (4)) (TableTree.leaf (5))))) (TableTree.node 503 (TableTree.node 501 (TableTree.leaf (5)) (TableTree.node 502 (TableTree.leaf (4)) (TableTree.leaf (5)))) (TableTree.node 505 (TableTree.node 504 (TableTree.leaf (6)) (TableTree.leaf (6))) (TableTree.node 506 (TableTree.leaf (7)) (TableTree.leaf (7)))))) (TableTree.node 514 (TableTree.node 510 (TableTree.node 508 (TableTree.leaf (6)) (TableTree.node 509 (TableTree.leaf (7)) (TableTree.leaf (4)))) (TableTree.node 512 (TableTree.node 511 (TableTree.leaf (5)) (TableTree.leaf (6))) (TableTree.node 513 (TableTree.leaf (7)) (TableTree.leaf (8))))) (TableTree.node 518 (TableTree.node 516 (TableTree.node 515 (TableTree.leaf (8)) (TableTree.leaf (0))) (TableTree.node 517 (TableTree.leaf (8)) (TableTree.leaf (1)))) (TableTree.node 520 (TableTree.node 519 (TableTree.leaf (2)) (TableTree.leaf (1))) (TableTree.node 521 (TableTree.leaf (2)) (TableTree.leaf (8)))))))) (TableTree.node 551 (TableTree.node 536 (TableTree.node 529 (TableTree.node 525 (TableTree.node 523 (TableTree.leaf (4)) (TableTree.node 524 (TableTree.leaf (5)) (TableTree.leaf (6)))) (TableTree.node 527 (TableTree.node 526 (TableTree.leaf (7)) (TableTree.leaf (8))) (TableTree.node 528 (TableTree.leaf (3)) (TableTree.leaf (4))))) (TableTree.node 532 (TableTree.node 530 (TableTree.leaf (5)) (TableTree.node 531 (TableTree.leaf (6)) (TableTree.leaf (6)))) (TableTree.node 534 (TableTree.node 533 (TableTree.leaf (7)) (TableTree.leaf (8))) (TableTree.node 535 (TableTree.leaf (7)) (TableTree.leaf (8)))))) (TableTree.node 543 (TableTree.node 539 (TableTree.node 537 (TableTree.leaf (0)) (TableTree.node 538 (TableTree.leaf (1)) (TableTree.leaf (0)))) (TableTree.node 541 (TableTree.node 540 (TableTree.leaf (0)) (TableTree.leaf (1))) (TableTree.node 542 (TableTree.leaf (1)) (TableTree.leaf (0))))) (TableTree.node 547 (TableTree.node 545 (TableTree.node 544 (TableTree.leaf (1)) (TableTree.leaf (3))) (TableTree.node 546 (TableTree.leaf (4)) (TableTree.leaf (5)))) (TableTree.node 549 (TableTree.node 548 (TableTree.leaf (6)) (TableTree.leaf (7))) (TableTree.node 550 (TableTree.leaf (8)) (TableTree.leaf (0))))))) (TableTree.node 565 (TableTree.node 558 (TableTree.node 554 (TableTree.node 552 (TableTree.leaf (1)) (TableTree.node 553 (TableTree.leaf (2)) (TableTree.leaf (3)))) (TableTree.node 556 (TableTree.node 555 (TableTree.leaf (4)) (TableTree.leaf (5))) (TableTree.node 557 (TableTree.leaf (2)) (TableTree.leaf (2))))) (TableTree.node 561 (TableTree.node 559 (TableTree.leaf (3)) (TableTree.node 560 (TableTree.leaf (3)) (TableTree.leaf (2)))) (TableTree.node 563 (TableTree.node 562 (TableTree.leaf (3)) (TableTree.leaf (4))) (TableTree.node 564 (TableTree.leaf (4)) (TableTree.leaf (5)))))) (TableTree.node 572 (TableTree.node 568 (TableTree.node 566 (TableTree.leaf (5)) (TableTree.node 567 (TableTree.leaf (4)) (TableTree.leaf (5)))) (TableTree.node 570 (TableTree.node 569 (TableTree.leaf (6)) (TableTree.leaf (7))) (TableTree.node 571 (TableTree.leaf (8)) (TableTree.leaf (0))))) (TableTree.node 576 (TableTree.node 574 (TableTree.node 573 (TableTree.leaf (6)) (TableTree.leaf (6))) (TableTree.node 575 (TableTree.leaf (7)) (TableTree.leaf (7)))) (TableTree.node 578 (TableTree.node 577 (TableTree.leaf (6)) (TableTree.leaf (7))) (TableTree.node 579 (TableTree.leaf (8)) (TableTree.leaf (8))))))))) (TableTree.node 638 (TableTree.node 609 (TableTree.node 594 (TableTree.node 587 (TableTree.node 583 (TableTree.node 581 (TableTree.leaf (0)) (TableTree.node 582 (TableTree.leaf (8)) (TableTree.leaf (0)))) (TableTree.node 585 (TableTree.node 584 (TableTree.leaf (0)) (TableTree.leaf (2))) (TableTree.node 586 (TableTree.leaf (3)) (TableTree.leaf (4))))) (TableTree.node 590 (TableTree.node 588 (TableTree.leaf (5)) (TableTree.node 589 (TableTree.leaf (6)) (TableTree.leaf (7)))) (TableTree.node 592 (TableTree.node 591 (TableTree.leaf (8)) (TableTree.leaf (1))) (TableTree.node 593 (TableTree.leaf (2)) (TableTree.leaf (3)))))) (TableTree.node 601 (TableTree.node 597 (TableTree.node 595 (TableTree.leaf (4)) (TableTree.node 596 (TableTree.leaf (1)) (TableTree.leaf (2)))) (TableTree.node 599 (TableTree.node 598 (TableTree.leaf (1)) (TableTree.leaf (1))) (TableTree.node 600 (TableTree.leaf (2)) (TableTree.leaf (2))))) (TableTree.node 605 (TableTree.node 603 (TableTree.node 602 (TableTree.leaf (3)) (TableTree.leaf (4))) (TableTree.node 604 (TableTree.leaf (3)) (TableTree.leaf (3)))) (TableTree.node 607 (TableTree.node 606 (TableTree.leaf (4)) (TableTree.leaf (4))) (TableTree.node 608 (TableTree.leaf (5)) (TableTree.leaf (6))))))) (TableTree.node 623 (TableTree.node 616 (TableTree.node 612 (TableTree.node 610 (TableTree.leaf (7)) (TableTree.node 611 (TableTree.leaf (8)) (TableTree.leaf (5)))) (TableTree.node 614 (TableTree.node 613 (TableTree.leaf (6)) (TableTree.leaf (5))) (TableTree.node 615 (TableTree.leaf (5)) (TableTree.leaf (6))))) (TableTree.node 619 (TableTree.node 617 (TableTree.leaf (6)) (TableTree.node 618 (TableTree.leaf (7)) (TableTree.leaf (8)))) (TableTree.node 621 (TableTree.node 620 (TableTree.leaf (7)) (TableTree.leaf (7))) (TableTree.node 622 (TableTree.leaf (8)) (TableTree.leaf (8)))))) (TableTree.node 630 (TableTree.node 626 (TableTree.node 624 (TableTree.leaf (1)) (TableTree.node 625 (TableTree.leaf (2)) (TableTree.leaf (3)))) (TableTree.node 628 (TableTree.node 627 (TableTree.leaf (4)) (TableTree.leaf (5))) (TableTree.node 629 (TableTree.leaf (6)) (TableTree.leaf (7))))) (TableTree.node 634 (TableTree.node 632 (TableTree.node 631 (TableTree.leaf (8)) (TableTree.leaf (1))) (TableTree.node 633 (TableTree.leaf (1)) (TableTree.leaf (2)))) (TableTree.node 636 (TableTree.node 635 (TableTree.leaf (3)) (TableTree.leaf (4))) (TableTree.node 637 (TableTree.leaf (5)) (TableTree.leaf (5)))))))) (TableTree.node 667 (TableTree.node 652 (TableTree.node 645 (TableTree.node 641 (TableTree.node 639 (TableTree.leaf (6)) (TableTree.node 640 (TableTree.leaf (6)) (TableTree.leaf (7)))) (TableTree.node 643 (TableTree.node 642 (TableTree.leaf (8)) (TableTree.leaf (0))) (TableTree.node 644 (TableTree.leaf (0)) (TableTree.leaf (1))))) (TableTree.node 648 (TableTree.node 646 (TableTree.leaf (1)) (TableTree.node 647 (TableTree.leaf (0)) (TableTree.leaf (1)))) (TableTree.node 650 (TableTree.node 649 (TableTree.leaf (2)) (TableTree.leaf (2))) (TableTree.node 651 (TableTree.leaf (3)) (TableTree.leaf (3)))))) (TableTree.node 659 (TableTree.node 655 (TableTree.node 653 (TableTree.leaf (2)) (TableTree.node 654 (TableTree.leaf (3)) (TableTree.leaf (0)))) (TableTree.node 657 (TableTree.node 656 (TableTree.leaf (1)) (TableTree.leaf (2))) (TableTree.node 658 (TableTree.leaf (3)) (TableTree.leaf (4))))) (TableTree.node 663 (TableTree.node 661 (TableTree.node 660 (TableTree.leaf (4)) (TableTree.leaf (5))) (TableTree.node 662 (TableTree.leaf (5)) (TableTree.leaf (4)))) (TableTree.node 665 (TableTree.node 664 (TableTree.leaf (5)) (TableTree.leaf (6))) (TableTree.node 666 (TableTree.leaf (6)) (TableTree.leaf (7))))))) (TableTree.node 681 (TableTree.node 674 (TableTree.node 670 (TableTree.node 668 (TableTree.leaf (7)) (TableTree.node 669 (TableTree.leaf (6)) (TableTree.leaf (7)))) (TableTree.node 672 (TableTree.node 671 (TableTree.leaf (4)) (TableTree.leaf (5))) (TableTree.node 673 (TableTree.leaf (6)) (TableTree.leaf (7))))) (TableTree.node 677 (TableTree.node 675 (TableTree.leaf (8)) (TableTree.node 676 (TableTree.leaf (8)) (TableTree.leaf (0)))) (TableTree.node 679 (TableTree.node 678 (TableTree.leaf (8)) (TableTree.leaf (1))) (TableTree.node 680 (TableTree.leaf (2)) (TableTree.leaf (1)))))) (TableTree.node 688 (TableTree.node 684 (TableTree.node 682 (TableTree.leaf (2)) (TableTree.node 683 (TableTree.leaf (8)) (TableTree.leaf (0)))) (TableTree.node 686 (TableTree.node 685 (TableTree.leaf (1)) (TableTree.leaf (2))) (TableTree.node 687 (TableTree.leaf (3)) (TableTree.leaf (4))))) (TableTree.node 692 (TableTree.node 690 (TableTree.node 689 (TableTree.leaf (3)) (TableTree.leaf (5))) (TableTree.node 691 (TableTree.leaf (6)) (TableTree.leaf (6)))) (TableTree.node 694 (TableTree.node 693 (TableTree.leaf (3)) (TableTree.leaf (4))) (TableTree.node 695 (TableTree.leaf (5)) (TableTree.leaf (6)))))))))) (TableTree.node 812 (TableTree.node 754 (TableTree.node 725 (TableTree.node 710 (TableTree.node 703 (TableTree.node 699 (TableTree.node 697 (TableTree.leaf (7)) (TableTree.node 698 (TableTree.leaf (8)) (TableTree.leaf (7)))) (TableTree.node 701 (TableTree.node 700 (TableTree.leaf (8)) (TableTree.leaf (0))) (TableTree.node 702 (TableTree.leaf (1)) (TableTree.leaf (7))))) (TableTree.node 706 (TableTree.node 704 (TableTree.leaf (8)) (TableTree.node 705 (TableTree.leaf (2)) (TableTree.leaf (3)))) (TableTree.node 708 (TableTree.node 707 (TableTree.leaf (4)) (TableTree.leaf (5))) (TableTree.node 709 (TableTree.leaf (6)) (TableTree.leaf (7)))))) (TableTree.node 717 (TableTree.node 713 (TableTree.node 711 (TableTree.leaf (8)) (TableTree.node 712 (TableTree.leaf (5)) (TableTree.leaf (8)))) (TableTree.node 715 (TableTree.node 714 (TableTree.leaf (0)) (TableTree.leaf (1))) (TableTree.node 716 (TableTree.leaf (2)) (TableTree.leaf (3))))) (TableTree.node 721 (TableTree.node 719 (TableTree.node 718 (TableTree.leaf (4)) (TableTree.leaf (5))) (TableTree.node 720 (TableTree.leaf (6)) (TableTree.leaf (7)))) (TableTree.node 723 (TableTree.node 722 (TableTree.leaf (8)) (TableTree.leaf (0))) (TableTree.node 724 (TableTree.leaf (1)) (TableTree.leaf (2))))))) (TableTree.node 739 (TableTree.node 732 (TableTree.node 728 (TableTree.node 726 (TableTree.leaf (6)) (TableTree.node 727 (TableTree.leaf (7)) (TableTree.leaf (2)))) (TableTree.node 730 (TableTree.node 729 (TableTree.leaf (2)) (TableTree.leaf (3))) (TableTree.node 731 (TableTree.leaf (3)) (TableTree.leaf (2))))) (TableTree.node 735 (TableTree.node 733 (TableTree.leaf (3)) (TableTree.node 734 (TableTree.leaf (4)) (TableTree.leaf (5)))) (TableTree.node 737 (TableTree.node 736 (TableTree.leaf (1)) (TableTree.leaf (4))) (TableTree.node 738 (TableTree.leaf (5)) (TableTree.leaf (7)))))) (TableTree.node 746 (TableTree.node 742 (TableTree.node 740 (TableTree.leaf (7)) (TableTree.node 741 (TableTree.leaf (8)) (TableTree.leaf (1)))) (TableTree.node 744 (TableTree.node 743 (TableTree.leaf (2)) (TableTree.leaf (1))) (TableTree.node 745 (TableTree.leaf (3)) (TableTree.leaf (4))))) (TableTree.node 750 (TableTree.node 748 (TableTree.node 747 (TableTree.leaf (3)) (TableTree.leaf (6))) (TableTree.node 749 (TableTree.leaf (8)) (TableTree.leaf (4)))) (TableTree.node 752 (TableTree.node 751 (TableTree.leaf (0)) (TableTree.leaf (1))) (TableTree.node 753 (TableTree.leaf (2)) (TableTree.leaf (2)))))))) (TableTree.node 783 (TableTree.node 768 (TableTree.node 761 (TableTree.node 757 (TableTree.node 755 (TableTree.leaf (3)) (TableTree.node 756 (TableTree.leaf (3)) (TableTree.leaf (2)))) (TableTree.node 759 (TableTree.node 758 (TableTree.leaf (3)) (TableTree.leaf (4))) (TableTree.node 760 (TableTree.leaf (4)) (TableTree.leaf (5))))) (TableTree.node 764 (TableTree.node 762 (TableTree.leaf (5)) (TableTree.node 763 (TableTree.leaf (4)) (TableTree.leaf (5)))) (TableTree.node 766 (TableTree.node 765 (TableTree.leaf (6)) (TableTree.leaf (6))) (TableTree.node 767 (TableTree.leaf (7)) (TableTree.leaf (7)))))) (TableTree.node 775 (TableTree.node 771 (TableTree.node 769 (TableTree.leaf (6)) (TableTree.node 770 (TableTree.leaf (7)) (TableTree.leaf (8)))) (TableTree.node 773 (TableTree.node 772 (TableTree.leaf (5)) (TableTree.leaf (6))) (TableTree.node 774 (TableTree.leaf (2)) (TableTree.leaf (3))))) (TableTree.node 779 (TableTree.node 777 (TableTree.node 776 (TableTree.leaf (4)) (TableTree.leaf (3))) (TableTree.node 778 (TableTree.leaf (4)) (TableTree.leaf (6)))) (TableTree.node 781 (TableTree.node 780 (TableTree.leaf (7)) (TableTree.leaf (8))) (TableTree.node 782 (TableTree.leaf (0)) (TableTree.leaf (3))))))) (TableTree.node 797 (TableTree.node 790 (TableTree.node 786 (TableTree.node 784 (TableTree.leaf (8)) (TableTree.node 785 (TableTree.leaf (4)) (TableTree.leaf (4)))) (TableTree.node 788 (TableTree.node 787 (TableTree.leaf (5)) (TableTree.leaf (5))) (TableTree.node 789 (TableTree.leaf (4)) (TableTree.leaf (5))))) (TableTree.node 793 (TableTree.node 791 (TableTree.leaf (6)) (TableTree.node 792 (TableTree.leaf (7)) (TableTree.leaf (7)))) (TableTree.node 795 (TableTree.node 794 (TableTree.leaf (6)) (TableTree.leaf (7))) (TableTree.node 796 (TableTree.leaf (2)) (TableTree.leaf (3)))))) (TableTree.node 804 (TableTree.node 800 (TableTree.node 798 (TableTree.leaf (4)) (TableTree.node 799 (TableTree.leaf (3)) (TableTree.leaf (6)))) (TableTree.node 802 (TableTree.node 801 (TableTree.leaf (7)) (TableTree.leaf (8))) (TableTree.node 803 (TableTree.leaf (8)) (TableTree.leaf (8))))) (TableTree.node 808 (TableTree.node 806 (TableTree.node 805 (TableTree.leaf (0)) (TableTree.leaf (8))) (TableTree.node 807 (TableTree.leaf (1)) (TableTree.leaf (2)))) (TableTree.node 810 (TableTree.node 809 (TableTree.leaf (6)) (TableTree.leaf (0))) (TableTree.node 811 (TableTree.leaf (1)) (TableTree.leaf (2))))))))) (TableTree.node 870 (TableTree.node 841 (TableTree.node 826 (TableTree.node 819 (TableTree.node 815 (TableTree.node 813 (TableTree.leaf (0)) (TableTree.node 814 (TableTree.leaf (1)) (TableTree.leaf (2)))) (TableTree.node 817 (TableTree.node 816 (TableTree.leaf (3)) (TableTree.leaf (4))) (TableTree.node 818 (TableTree.leaf (5)) (TableTree.leaf (6))))) (TableTree.node 822 (TableTree.node 820 (TableTree.leaf (7)) (TableTree.node 821 (TableTree.leaf (8)) (TableTree.leaf (0)))) (TableTree.node 824 (TableTree.node 823 (TableTree.leaf (0)) (TableTree.leaf (0))) (TableTree.node 825 (TableTree.leaf (1)) (TableTree.leaf (2)))))) (TableTree.node 833 (TableTree.node 829 (TableTree.node 827 (TableTree.leaf (3)) (TableTree.node 828 (TableTree.leaf (2)) (TableTree.leaf (2)))) (TableTree.node 831 (TableTree.node 830 (TableTree.leaf (3)) (TableTree.leaf (3))) (TableTree.node 832 (TableTree.leaf (2)) (TableTree.leaf (3))))) (TableTree.node 837 (TableTree.node 835 (TableTree.node 834 (TableTree.leaf (4)) (TableTree.leaf (4))) (TableTree.node 836 (TableTree.leaf (5)) (TableTree.leaf (5)))) (TableTree.node 839 (TableTree.node 838 (TableTree.leaf (4)) (TableTree.leaf (5))) (TableTree.node 840 (TableTree.leaf (6)) (TableTree.leaf (6))))))) (TableTree.node 855 (TableTree.node 848 (TableTree.node 844 (TableTree.node 842 (TableTree.leaf (6)) (TableTree.node 843 (TableTree.leaf (7)) (TableTree.leaf (7)))) (TableTree.node 846 (TableTree.node 845 (TableTree.leaf (6)) (TableTree.leaf (7))) (TableTree.node 847 (TableTree.leaf (8)) (TableTree.leaf (8))))) (TableTree.node 851 (TableTree.node 849 (TableTree.leaf (8)) (TableTree.node 850 (TableTree.leaf (1)) (TableTree.leaf (2)))) (TableTree.node 853 (TableTree.node 852 (TableTree.leaf (1)) (TableTree.leaf (2))) (TableTree.node 854 (TableTree.leaf (1)) (TableTree.leaf (3)))))) (TableTree.node 862 (TableTree.node 858 (TableTree.node 856 (TableTree.leaf (5)) (TableTree.node 857 (TableTree.leaf (6)) (TableTree.leaf (5)))) (TableTree.node 860 (TableTree.node 859 (TableTree.leaf (6)) (TableTree.leaf (7))) (TableTree.node 861 (TableTree.leaf (8)) (TableTree.leaf (0))))) (TableTree.node 866 (TableTree.node 864 (TableTree.node 863 (TableTree.leaf (8)) (TableTree.leaf (6))) (TableTree.node 865 (TableTree.leaf (7)) (TableTree.leaf (0)))) (TableTree.node 868 (TableTree.node 867 (TableTree.leaf (2)) (TableTree.leaf (3))) (TableTree.node 869 (TableTree.leaf (6)) (TableTree.leaf (5)))))))) (TableTree.node 899 (TableTree.node 884 (TableTree.node 877 (TableTree.node 873 (TableTree.node 871 (TableTree.leaf (4)) (TableTree.node 872 (TableTree.leaf (5)) (TableTree.leaf (4)))) (TableTree.node 875 (TableTree.node 874 (TableTree.leaf (5)) (TableTree.leaf (8))) (TableTree.node 876 (TableTree.leaf (1)) (TableTree.leaf (1))))) (TableTree.node 880 (TableTree.node 878 (TableTree.leaf (3)) (TableTree.node 879 (TableTree.leaf (4)) (TableTree.leaf (3)))) (TableTree.node 882 (TableTree.node 881 (TableTree.leaf (8)) (TableTree.leaf (2))) (TableTree.node 883 (TableTree.leaf (6)) (TableTree.leaf (7)))))) (TableTree.node 891 (TableTree.node 887 (TableTree.node 885 (TableTree.leaf (8)) (TableTree.node 886 (TableTree.leaf (0)) (TableTree.leaf (1)))) (TableTree.node 889 (TableTree.node 888 (TableTree.leaf (2)) (TableTree.leaf (3))) (TableTree.node 890 (TableTree.leaf (4)) (TableTree.leaf (5))))) (TableTree.node 895 (TableTree.node 893 (TableTree.node 892 (TableTree.leaf (6)) (TableTree.leaf (7))) (TableTree.node 894 (TableTree.leaf (8)) (TableTree.leaf (0)))) (TableTree.node 897 (TableTree.node 896 (TableTree.leaf (1)) (TableTree.leaf (2))) (TableTree.node 898 (TableTree.leaf (3)) (TableTree.leaf (4))))))) (TableTree.node 914 (TableTree.node 906 (TableTree.node 902 (TableTree.node 900 (TableTree.leaf (5)) (TableTree.node 901 (TableTree.leaf (6)) (TableTree.leaf (7)))) (TableTree.node 904 (TableTree.node 903 (TableTree.leaf (8)) (TableTree.leaf (0))) (TableTree.node 905 (TableTree.leaf (1)) (TableTree.leaf (2))))) (TableTree.node 910 (TableTree.node 908 (TableTree.node 907 (TableTree.leaf (3)) (TableTree.leaf (4))) (TableTree.node 909 (TableTree.leaf (5)) (TableTree.leaf (6)))) (TableTree.node 912 (TableTree.node 911 (TableTree.leaf (7)) (TableTree.leaf (8))) (TableTree.node 913 (TableTree.leaf (0)) (TableTree.leaf (1)))))) (TableTree.node 921 (TableTree.node 917 (TableTree.node 915 (TableTree.leaf (2)) (TableTree.node 916 (TableTree.leaf (3)) (TableTree.leaf (4)))) (TableTree.node 919 (TableTree.node 918 (TableTree.leaf (5)) (TableTree.leaf (6))) (TableTree.node 920 (TableTree.leaf (7)) (TableTree.leaf (8))))) (TableTree.node 925 (TableTree.node 923 (TableTree.node 922 (TableTree.leaf (0)) (TableTree.leaf (2))) (TableTree.node 924 (TableTree.leaf (3)) (TableTree.leaf (4)))) (TableTree.node 927 (TableTree.node 926 (TableTree.leaf (5)) (TableTree.leaf (6))) (TableTree.node 928 (TableTree.leaf (7)) (TableTree.leaf (8))))))))))))
private def carryAt (i : ℕ) : ℕ := if i < 929 then TableTree.lookup carryAtTree i else 0
private def endAtTree : TableTree ((List ℕ)) := (TableTree.node 464 (TableTree.node 232 (TableTree.node 116 (TableTree.node 58 (TableTree.node 29 (TableTree.node 14 (TableTree.node 7 (TableTree.node 3 (TableTree.node 1 (TableTree.leaf ([0])) (TableTree.node 2 (TableTree.leaf ([1])) (TableTree.leaf ([2])))) (TableTree.node 5 (TableTree.node 4 (TableTree.leaf ([3])) (TableTree.leaf ([5]))) (TableTree.node 6 (TableTree.leaf ([7])) (TableTree.leaf ([8]))))) (TableTree.node 10 (TableTree.node 8 (TableTree.leaf ([10])) (TableTree.node 9 (TableTree.leaf ([13])) (TableTree.leaf ([15])))) (TableTree.node 12 (TableTree.node 11 (TableTree.leaf ([18])) (TableTree.leaf ([20]))) (TableTree.node 13 (TableTree.leaf ([21])) (TableTree.leaf ([23])))))) (TableTree.node 21 (TableTree.node 17 (TableTree.node 15 (TableTree.leaf ([27])) (TableTree.node 16 (TableTree.leaf ([29])) (TableTree.leaf ([20])))) (TableTree.node 19 (TableTree.node 18 (TableTree.leaf ([35])) (TableTree.leaf ([39]))) (TableTree.node 20 (TableTree.leaf ([20])) (TableTree.leaf ([35]))))) (TableTree.node 25 (TableTree.node 23 (TableTree.node 22 (TableTree.leaf ([35])) (TableTree.leaf ([44]))) (TableTree.node 24 (TableTree.leaf ([44])) (TableTree.leaf ([44])))) (TableTree.node 27 (TableTree.node 26 (TableTree.leaf ([44])) (TableTree.leaf ([44]))) (TableTree.node 28 (TableTree.leaf ([47])) (TableTree.leaf ([46]))))))) (TableTree.node 43 (TableTree.node 36 (TableTree.node 32 (TableTree.node 30 (TableTree.leaf ([54])) (TableTree.node 31 (TableTree.leaf ([54])) (TableTree.leaf ([35])))) (TableTree.node 34 (TableTree.node 33 (TableTree.leaf ([34])) (TableTree.leaf ([58]))) (TableTree.node 35 (TableTree.leaf ([58])) (TableTree.leaf ([60]))))) (TableTree.node 39 (TableTree.node 37 (TableTree.leaf ([59])) (TableTree.node 38 (TableTree.leaf ([44])) (TableTree.leaf ([44])))) (TableTree.node 41 (TableTree.node 40 (TableTree.leaf ([44])) (TableTree.leaf ([42]))) (TableTree.node 42 (TableTree.leaf ([20])) (TableTree.leaf ([20])))))) (TableTree.node 50 (TableTree.node 46 (TableTree.node 44 (TableTree.leaf ([44])) (TableTree.node 45 (TableTree.leaf ([42])) (TableTree.leaf ([69])))) (TableTree.node 48 (TableTree.node 47 (TableTree.leaf ([21])) (TableTree.leaf ([44]))) (TableTree.node 49 (TableTree.leaf ([44])) (TableTree.leaf ([20]))))) (TableTree.node 54 (TableTree.node 52 (TableTree.node 51 (TableTree.leaf ([44])) (TableTree.leaf ([20]))) (TableTree.node 53 (TableTree.leaf ([44])) (TableTree.leaf ([44])))) (TableTree.node 56 (TableTree.node 55 (TableTree.leaf ([42])) (TableTree.leaf ([44]))) (TableTree.node 57 (TableTree.leaf ([44])) (TableTree.leaf ([44])))))))) (TableTree.node 87 (TableTree.node 72 (TableTree.node 65 (TableTree.node 61 (TableTree.node 59 (TableTree.leaf ([42])) (TableTree.node 60 (TableTree.leaf ([44])) (TableTree.leaf ([44])))) (TableTree.node 63 (TableTree.node 62 (TableTree.leaf ([44])) (TableTree.leaf ([42]))) (TableTree.node 64 (TableTree.leaf ([44])) (TableTree.leaf ([44]))))) (TableTree.node 68 (TableTree.node 66 (TableTree.leaf ([44])) (TableTree.node 67 (TableTree.leaf ([42])) (TableTree.leaf ([44])))) (TableTree.node 70 (TableTree.node 69 (TableTree.leaf ([44])) (TableTree.leaf ([44]))) (TableTree.node 71 (TableTree.leaf ([42])) (TableTree.leaf ([44])))))) (TableTree.node 79 (TableTree.node 75 (TableTree.node 73 (TableTree.leaf ([44])) (TableTree.node 74 (TableTree.leaf ([44])) (TableTree.leaf ([42])))) (TableTree.node 77 (TableTree.node 76 (TableTree.leaf ([43])) (TableTree.leaf ([20]))) (TableTree.node 78 (TableTree.leaf ([44])) (TableTree.leaf ([20]))))) (TableTree.node 83 (TableTree.node 81 (TableTree.node 80 (TableTree.leaf ([42])) (TableTree.leaf ([20]))) (TableTree.node 82 (TableTree.leaf ([44])) (TableTree.leaf ([38])))) (TableTree.node 85 (TableTree.node 84 (TableTree.leaf ([43])) (TableTree.leaf ([44]))) (TableTree.node 86 (TableTree.leaf ([44])) (TableTree.leaf ([44]))))))) (TableTree.node 101 (TableTree.node 94 (TableTree.node 90 (TableTree.node 88 (TableTree.leaf ([44])) (TableTree.node 89 (TableTree.leaf ([44])) (TableTree.leaf ([42])))) (TableTree.node 92 (TableTree.node 91 (TableTree.leaf ([44])) (TableTree.leaf ([42]))) (TableTree.node 93 (TableTree.leaf ([43])) (TableTree.leaf ([44]))))) (TableTree.node 97 (TableTree.node 95 (TableTree.leaf ([44])) (TableTree.node 96 (TableTree.leaf ([44])) (TableTree.leaf ([44])))) (TableTree.node 99 (TableTree.node 98 (TableTree.leaf ([44])) (TableTree.leaf ([42]))) (TableTree.node 100 (TableTree.leaf ([44])) (TableTree.leaf ([44])))))) (TableTree.node 108 (TableTree.node 104 (TableTree.node 102 (TableTree.leaf ([44])) (TableTree.node 103 (TableTree.leaf ([44])) (TableTree.leaf ([42])))) (TableTree.node 106 (TableTree.node 105 (TableTree.leaf ([43])) (TableTree.leaf ([44]))) (TableTree.node 107 (TableTree.leaf ([44])) (TableTree.leaf ([42]))))) (TableTree.node 112 (TableTree.node 110 (TableTree.node 109 (TableTree.leaf ([44])) (TableTree.leaf ([44]))) (TableTree.node 111 (TableTree.leaf ([42])) (TableTree.leaf ([44])))) (TableTree.node 114 (TableTree.node 113 (TableTree.leaf ([44])) (TableTree.leaf ([44]))) (TableTree.node 115 (TableTree.leaf ([44])) (TableTree.leaf ([43]))))))))) (TableTree.node 174 (TableTree.node 145 (TableTree.node 130 (TableTree.node 123 (TableTree.node 119 (TableTree.node 117 (TableTree.leaf ([43])) (TableTree.node 118 (TableTree.leaf ([44])) (TableTree.leaf ([44])))) (TableTree.node 121 (TableTree.node 120 (TableTree.leaf ([44])) (TableTree.leaf ([44]))) (TableTree.node 122 (TableTree.leaf ([44])) (TableTree.leaf ([44]))))) (TableTree.node 126 (TableTree.node 124 (TableTree.leaf ([44])) (TableTree.node 125 (TableTree.leaf ([44])) (TableTree.leaf ([44])))) (TableTree.node 128 (TableTree.node 127 (TableTree.leaf ([42])) (TableTree.leaf ([44]))) (TableTree.node 129 (TableTree.leaf ([44])) (TableTree.leaf ([44])))))) (TableTree.node 137 (TableTree.node 133 (TableTree.node 131 (TableTree.leaf ([44])) (TableTree.node 132 (TableTree.leaf ([44])) (TableTree.leaf ([44])))) (TableTree.node 135 (TableTree.node 134 (TableTree.leaf ([44])) (TableTree.leaf ([44]))) (TableTree.node 136 (TableTree.leaf ([44])) (TableTree.leaf ([44]))))) (TableTree.node 141 (TableTree.node 139 (TableTree.node 138 (TableTree.leaf ([44])) (TableTree.leaf ([42]))) (TableTree.node 140 (TableTree.leaf ([44])) (TableTree.leaf ([44])))) (TableTree.node 143 (TableTree.node 142 (TableTree.leaf ([44])) (TableTree.leaf ([44]))) (TableTree.node 144 (TableTree.leaf ([44])) (TableTree.leaf ([42]))))))) (TableTree.node 159 (TableTree.node 152 (TableTree.node 148 (TableTree.node 146 (TableTree.leaf ([43])) (TableTree.node 147 (TableTree.leaf ([44])) (TableTree.leaf ([44])))) (TableTree.node 150 (TableTree.node 149 (TableTree.leaf ([44])) (TableTree.leaf ([42]))) (TableTree.node 151 (TableTree.leaf ([44])) (TableTree.leaf ([44]))))) (TableTree.node 155 (TableTree.node 153 (TableTree.leaf ([43])) (TableTree.node 154 (TableTree.leaf ([43])) (TableTree.leaf ([44])))) (TableTree.node 157 (TableTree.node 156 (TableTree.leaf ([44])) (TableTree.leaf ([44]))) (TableTree.node 158 (TableTree.leaf ([44])) (TableTree.leaf ([44])))))) (TableTree.node 166 (TableTree.node 162 (TableTree.node 160 (TableTree.leaf ([44])) (TableTree.node 161 (TableTree.leaf ([42])) (TableTree.leaf ([43])))) (TableTree.node 164 (TableTree.node 163 (TableTree.leaf ([44])) (TableTree.leaf ([42]))) (TableTree.node 165 (TableTree.leaf ([44])) (TableTree.leaf ([44]))))) (TableTree.node 170 (TableTree.node 168 (TableTree.node 167 (TableTree.leaf ([42])) (TableTree.leaf ([44]))) (TableTree.node 169 (TableTree.leaf ([44])) (TableTree.leaf ([44])))) (TableTree.node 172 (TableTree.node 171 (TableTree.leaf ([44])) (TableTree.leaf ([42]))) (TableTree.node 173 (TableTree.leaf ([43])) (TableTree.leaf ([44])))))))) (TableTree.node 203 (TableTree.node 188 (TableTree.node 181 (TableTree.node 177 (TableTree.node 175 (TableTree.leaf ([44])) (TableTree.node 176 (TableTree.leaf ([44])) (TableTree.leaf ([44])))) (TableTree.node 179 (TableTree.node 178 (TableTree.leaf ([44])) (TableTree.leaf ([42]))) (TableTree.node 180 (TableTree.leaf ([44])) (TableTree.leaf ([44]))))) (TableTree.node 184 (TableTree.node 182 (TableTree.leaf ([42])) (TableTree.node 183 (TableTree.leaf ([44])) (TableTree.leaf ([43])))) (TableTree.node 186 (TableTree.node 185 (TableTree.leaf ([43])) (TableTree.leaf ([44]))) (TableTree.node 187 (TableTree.leaf ([44])) (TableTree.leaf ([44])))))) (TableTree.node 195 (TableTree.node 191 (TableTree.node 189 (TableTree.leaf ([44])) (TableTree.node 190 (TableTree.leaf ([44])) (TableTree.leaf ([44])))) (TableTree.node 193 (TableTree.node 192 (TableTree.leaf ([44])) (TableTree.leaf ([44]))) (TableTree.node 194 (TableTree.leaf ([42])) (TableTree.leaf ([43]))))) (TableTree.node 199 (TableTree.node 197 (TableTree.node 196 (TableTree.leaf ([68])) (TableTree.leaf ([41]))) (TableTree.node 198 (TableTree.leaf ([44])) (TableTree.leaf ([44])))) (TableTree.node 201 (TableTree.node 200 (TableTree.leaf ([44])) (TableTree.leaf ([44]))) (TableTree.node 202 (TableTree.leaf ([44])) (TableTree.leaf ([42]))))))) (TableTree.node 217 (TableTree.node 210 (TableTree.node 206 (TableTree.node 204 (TableTree.leaf ([42])) (TableTree.node 205 (TableTree.leaf ([43])) (TableTree.leaf ([44])))) (TableTree.node 208 (TableTree.node 207 (TableTree.leaf ([42])) (TableTree.leaf ([44]))) (TableTree.node 209 (TableTree.leaf ([44])) (TableTree.leaf ([44]))))) (TableTree.node 213 (TableTree.node 211 (TableTree.leaf ([44])) (TableTree.node 212 (TableTree.leaf ([44])) (TableTree.leaf ([68])))) (TableTree.node 215 (TableTree.node 214 (TableTree.leaf ([41])) (TableTree.leaf ([68]))) (TableTree.node 216 (TableTree.leaf ([41])) (TableTree.leaf ([44])))))) (TableTree.node 224 (TableTree.node 220 (TableTree.node 218 (TableTree.leaf ([44])) (TableTree.node 219 (TableTree.leaf ([44])) (TableTree.leaf ([44])))) (TableTree.node 222 (TableTree.node 221 (TableTree.leaf ([44])) (TableTree.leaf ([44]))) (TableTree.node 223 (TableTree.leaf ([42])) (TableTree.leaf ([44]))))) (TableTree.node 228 (TableTree.node 226 (TableTree.node 225 (TableTree.leaf ([44])) (TableTree.leaf ([44]))) (TableTree.node 227 (TableTree.leaf ([44])) (TableTree.leaf ([42])))) (TableTree.node 230 (TableTree.node 229 (TableTree.leaf ([44])) (TableTree.leaf ([44]))) (TableTree.node 231 (TableTree.leaf ([44])) (TableTree.leaf ([44])))))))))) (TableTree.node 348 (TableTree.node 290 (TableTree.node 261 (TableTree.node 246 (TableTree.node 239 (TableTree.node 235 (TableTree.node 233 (TableTree.leaf ([42])) (TableTree.node 234 (TableTree.leaf ([42])) (TableTree.leaf ([43])))) (TableTree.node 237 (TableTree.node 236 (TableTree.leaf ([43])) (TableTree.leaf ([44]))) (TableTree.node 238 (TableTree.leaf ([44])) (TableTree.leaf ([43]))))) (TableTree.node 242 (TableTree.node 240 (TableTree.leaf ([43])) (TableTree.node 241 (TableTree.leaf ([68])) (TableTree.leaf ([41])))) (TableTree.node 244 (TableTree.node 243 (TableTree.leaf ([44])) (TableTree.leaf ([44]))) (TableTree.node 245 (TableTree.leaf ([42])) (TableTree.leaf ([42])))))) (TableTree.node 253 (TableTree.node 249 (TableTree.node 247 (TableTree.leaf ([44])) (TableTree.node 248 (TableTree.leaf ([44])) (TableTree.leaf ([44])))) (TableTree.node 251 (TableTree.node 250 (TableTree.leaf ([44])) (TableTree.leaf ([42]))) (TableTree.node 252 (TableTree.leaf ([42])) (TableTree.leaf ([44]))))) (TableTree.node 257 (TableTree.node 255 (TableTree.node 254 (TableTree.leaf ([44])) (TableTree.leaf ([44]))) (TableTree.node 256 (TableTree.leaf ([42])) (TableTree.leaf ([43])))) (TableTree.node 259 (TableTree.node 258 (TableTree.leaf ([43])) (TableTree.leaf ([44]))) (TableTree.node 260 (TableTree.leaf ([44])) (TableTree.leaf ([44]))))))) (TableTree.node 275 (TableTree.node 268 (TableTree.node 264 (TableTree.node 262 (TableTree.leaf ([42])) (TableTree.node 263 (TableTree.leaf ([44])) (TableTree.leaf ([44])))) (TableTree.node 266 (TableTree.node 265 (TableTree.leaf ([44])) (TableTree.leaf ([44]))) (TableTree.node 267 (TableTree.leaf ([42])) (TableTree.leaf ([44]))))) (TableTree.node 271 (TableTree.node 269 (TableTree.leaf ([42])) (TableTree.node 270 (TableTree.leaf ([44])) (TableTree.leaf ([42])))) (TableTree.node 273 (TableTree.node 272 (TableTree.leaf ([43])) (TableTree.leaf ([68]))) (TableTree.node 274 (TableTree.leaf ([41])) (TableTree.leaf ([44])))))) (TableTree.node 282 (TableTree.node 278 (TableTree.node 276 (TableTree.leaf ([42])) (TableTree.node 277 (TableTree.leaf ([44])) (TableTree.leaf ([44])))) (TableTree.node 280 (TableTree.node 279 (TableTree.leaf ([44])) (TableTree.leaf ([44]))) (TableTree.node 281 (TableTree.leaf ([42])) (TableTree.leaf ([43]))))) (TableTree.node 286 (TableTree.node 284 (TableTree.node 283 (TableTree.leaf ([44])) (TableTree.leaf ([44]))) (TableTree.node 285 (TableTree.leaf ([44])) (TableTree.leaf ([44])))) (TableTree.node 288 (TableTree.node 287 (TableTree.leaf ([44])) (TableTree.leaf ([42]))) (TableTree.node 289 (TableTree.leaf ([42])) (TableTree.leaf ([43])))))))) (TableTree.node 319 (TableTree.node 304 (TableTree.node 297 (TableTree.node 293 (TableTree.node 291 (TableTree.leaf ([44])) (TableTree.node 292 (TableTree.leaf ([42])) (TableTree.leaf ([44])))) (TableTree.node 295 (TableTree.node 294 (TableTree.leaf ([44])) (TableTree.leaf ([42]))) (TableTree.node 296 (TableTree.leaf ([44])) (TableTree.leaf ([44]))))) (TableTree.node 300 (TableTree.node 298 (TableTree.leaf ([42])) (TableTree.node 299 (TableTree.leaf ([44])) (TableTree.leaf ([44])))) (TableTree.node 302 (TableTree.node 301 (TableTree.leaf ([44])) (TableTree.leaf ([44]))) (TableTree.node 303 (TableTree.leaf ([68])) (TableTree.leaf ([41])))))) (TableTree.node 311 (TableTree.node 307 (TableTree.node 305 (TableTree.leaf ([68])) (TableTree.node 306 (TableTree.leaf ([41])) (TableTree.leaf ([42])))) (TableTree.node 309 (TableTree.node 308 (TableTree.leaf ([44])) (TableTree.leaf ([44]))) (TableTree.node 310 (TableTree.leaf ([44])) (TableTree.leaf ([44]))))) (TableTree.node 315 (TableTree.node 313 (TableTree.node 312 (TableTree.leaf ([44])) (TableTree.leaf ([44]))) (TableTree.node 314 (TableTree.leaf ([44])) (TableTree.leaf ([44])))) (TableTree.node 317 (TableTree.node 316 (TableTree.leaf ([44])) (TableTree.leaf ([44]))) (TableTree.node 318 (TableTree.leaf ([44])) (TableTree.leaf ([42]))))))) (TableTree.node 333 (TableTree.node 326 (TableTree.node 322 (TableTree.node 320 (TableTree.leaf ([44])) (TableTree.node 321 (TableTree.leaf ([44])) (TableTree.leaf ([44])))) (TableTree.node 324 (TableTree.node 323 (TableTree.leaf ([44])) (TableTree.leaf ([44]))) (TableTree.node 325 (TableTree.leaf ([42])) (TableTree.leaf ([42]))))) (TableTree.node 329 (TableTree.node 327 (TableTree.leaf ([43])) (TableTree.node 328 (TableTree.leaf ([43])) (TableTree.leaf ([44])))) (TableTree.node 331 (TableTree.node 330 (TableTree.leaf ([44])) (TableTree.leaf ([44]))) (TableTree.node 332 (TableTree.leaf ([44])) (TableTree.leaf ([42])))))) (TableTree.node 340 (TableTree.node 336 (TableTree.node 334 (TableTree.leaf ([42])) (TableTree.node 335 (TableTree.leaf ([44])) (TableTree.leaf ([44])))) (TableTree.node 338 (TableTree.node 337 (TableTree.leaf ([44])) (TableTree.leaf ([44]))) (TableTree.node 339 (TableTree.leaf ([42])) (TableTree.leaf ([42]))))) (TableTree.node 344 (TableTree.node 342 (TableTree.node 341 (TableTree.leaf ([44])) (TableTree.leaf ([44]))) (TableTree.node 343 (TableTree.leaf ([44])) (TableTree.leaf ([44])))) (TableTree.node 346 (TableTree.node 345 (TableTree.leaf ([44])) (TableTree.leaf ([42]))) (TableTree.node 347 (TableTree.leaf ([44])) (TableTree.leaf ([44]))))))))) (TableTree.node 406 (TableTree.node 377 (TableTree.node 362 (TableTree.node 355 (TableTree.node 351 (TableTree.node 349 (TableTree.leaf ([44])) (TableTree.node 350 (TableTree.leaf ([44])) (TableTree.leaf ([42])))) (TableTree.node 353 (TableTree.node 352 (TableTree.leaf ([44])) (TableTree.leaf ([44]))) (TableTree.node 354 (TableTree.leaf ([42])) (TableTree.leaf ([42]))))) (TableTree.node 358 (TableTree.node 356 (TableTree.leaf ([43])) (TableTree.node 357 (TableTree.leaf ([44])) (TableTree.leaf ([42])))) (TableTree.node 360 (TableTree.node 359 (TableTree.leaf ([44])) (TableTree.leaf ([42]))) (TableTree.node 361 (TableTree.leaf ([42])) (TableTree.leaf ([43])))))) (TableTree.node 369 (TableTree.node 365 (TableTree.node 363 (TableTree.leaf ([68])) (TableTree.node 364 (TableTree.leaf ([41])) (TableTree.leaf ([44])))) (TableTree.node 367 (TableTree.node 366 (TableTree.leaf ([42])) (TableTree.leaf ([42]))) (TableTree.node 368 (TableTree.leaf ([43])) (TableTree.leaf ([68]))))) (TableTree.node 373 (TableTree.node 371 (TableTree.node 370 (TableTree.leaf ([41])) (TableTree.leaf ([68]))) (TableTree.node 372 (TableTree.leaf ([41])) (TableTree.leaf ([44])))) (TableTree.node 375 (TableTree.node 374 (TableTree.leaf ([44])) (TableTree.leaf ([43]))) (TableTree.node 376 (TableTree.leaf ([68])) (TableTree.leaf ([41]))))))) (TableTree.node 391 (TableTree.node 384 (TableTree.node 380 (TableTree.node 378 (TableTree.leaf ([42])) (TableTree.node 379 (TableTree.leaf ([42])) (TableTree.leaf ([43])))) (TableTree.node 382 (TableTree.node 381 (TableTree.leaf ([43])) (TableTree.leaf ([44]))) (TableTree.node 383 (TableTree.leaf ([44])) (TableTree.leaf ([44]))))) (TableTree.node 387 (TableTree.node 385 (TableTree.leaf ([42])) (TableTree.node 386 (TableTree.leaf ([43])) (TableTree.leaf ([43])))) (TableTree.node 389 (TableTree.node 388 (TableTree.leaf ([44])) (TableTree.leaf ([44]))) (TableTree.node 390 (TableTree.leaf ([42])) (TableTree.leaf ([42])))))) (TableTree.node 398 (TableTree.node 394 (TableTree.node 392 (TableTree.leaf ([44])) (TableTree.node 393 (TableTree.leaf ([44])) (TableTree.leaf ([44])))) (TableTree.node 396 (TableTree.node 395 (TableTree.leaf ([44])) (TableTree.leaf ([42]))) (TableTree.node 397 (TableTree.leaf ([42])) (TableTree.leaf ([44]))))) (TableTree.node 402 (TableTree.node 400 (TableTree.node 399 (TableTree.leaf ([44])) (TableTree.leaf ([42]))) (TableTree.node 401 (TableTree.leaf ([43])) (TableTree.leaf ([68])))) (TableTree.node 404 (TableTree.node 403 (TableTree.leaf ([41])) (TableTree.leaf ([44]))) (TableTree.node 405 (TableTree.leaf ([44])) (TableTree.leaf ([44])))))))) (TableTree.node 435 (TableTree.node 420 (TableTree.node 413 (TableTree.node 409 (TableTree.node 407 (TableTree.leaf ([42])) (TableTree.node 408 (TableTree.leaf ([44])) (TableTree.leaf ([44])))) (TableTree.node 411 (TableTree.node 410 (TableTree.leaf ([44])) (TableTree.leaf ([44]))) (TableTree.node 412 (TableTree.leaf ([44])) (TableTree.leaf ([44]))))) (TableTree.node 416 (TableTree.node 414 (TableTree.leaf ([42])) (TableTree.node 415 (TableTree.leaf ([44])) (TableTree.leaf ([42])))) (TableTree.node 418 (TableTree.node 417 (TableTree.leaf ([44])) (TableTree.leaf ([43]))) (TableTree.node 419 (TableTree.leaf ([44])) (TableTree.leaf ([68])))))) (TableTree.node 427 (TableTree.node 423 (TableTree.node 421 (TableTree.leaf ([41])) (TableTree.node 422 (TableTree.leaf ([68])) (TableTree.leaf ([41])))) (TableTree.node 425 (TableTree.node 424 (TableTree.leaf ([44])) (TableTree.leaf ([42]))) (TableTree.node 426 (TableTree.leaf ([44])) (TableTree.leaf ([42]))))) (TableTree.node 431 (TableTree.node 429 (TableTree.node 428 (TableTree.leaf ([44])) (TableTree.leaf ([42]))) (TableTree.node 430 (TableTree.leaf ([42])) (TableTree.leaf ([43])))) (TableTree.node 433 (TableTree.node 432 (TableTree.leaf ([68])) (TableTree.leaf ([41]))) (TableTree.node 434 (TableTree.leaf ([41])) (TableTree.leaf ([41]))))))) (TableTree.node 449 (TableTree.node 442 (TableTree.node 438 (TableTree.node 436 (TableTree.leaf ([41])) (TableTree.node 437 (TableTree.leaf ([44])) (TableTree.leaf ([43])))) (TableTree.node 440 (TableTree.node 439 (TableTree.leaf ([41])) (TableTree.leaf ([42]))) (TableTree.node 441 (TableTree.leaf ([42])) (TableTree.leaf ([44]))))) (TableTree.node 445 (TableTree.node 443 (TableTree.leaf ([44])) (TableTree.node 444 (TableTree.leaf ([42])) (TableTree.leaf ([44])))) (TableTree.node 447 (TableTree.node 446 (TableTree.leaf ([44])) (TableTree.leaf ([44]))) (TableTree.node 448 (TableTree.leaf ([44])) (TableTree.leaf ([42])))))) (TableTree.node 456 (TableTree.node 452 (TableTree.node 450 (TableTree.leaf ([43])) (TableTree.node 451 (TableTree.leaf ([44])) (TableTree.leaf ([44])))) (TableTree.node 454 (TableTree.node 453 (TableTree.leaf ([44])) (TableTree.leaf ([44]))) (TableTree.node 455 (TableTree.leaf ([44])) (TableTree.leaf ([44]))))) (TableTree.node 460 (TableTree.node 458 (TableTree.node 457 (TableTree.leaf ([42])) (TableTree.leaf ([44]))) (TableTree.node 459 (TableTree.leaf ([42])) (TableTree.leaf ([42])))) (TableTree.node 462 (TableTree.node 461 (TableTree.leaf ([43])) (TableTree.leaf ([44]))) (TableTree.node 463 (TableTree.leaf ([42])) (TableTree.leaf ([44]))))))))))) (TableTree.node 696 (TableTree.node 580 (TableTree.node 522 (TableTree.node 493 (TableTree.node 478 (TableTree.node 471 (TableTree.node 467 (TableTree.node 465 (TableTree.leaf ([44])) (TableTree.node 466 (TableTree.leaf ([42])) (TableTree.leaf ([44])))) (TableTree.node 469 (TableTree.node 468 (TableTree.leaf ([44])) (TableTree.leaf ([42]))) (TableTree.node 470 (TableTree.leaf ([44])) (TableTree.leaf ([44]))))) (TableTree.node 474 (TableTree.node 472 (TableTree.leaf ([44])) (TableTree.node 473 (TableTree.leaf ([44])) (TableTree.leaf ([42])))) (TableTree.node 476 (TableTree.node 475 (TableTree.leaf ([42])) (TableTree.leaf ([43]))) (TableTree.node 477 (TableTree.leaf ([43])) (TableTree.leaf ([42])))))) (TableTree.node 485 (TableTree.node 481 (TableTree.node 479 (TableTree.leaf ([43])) (TableTree.node 480 (TableTree.leaf ([68])) (TableTree.leaf ([68])))) (TableTree.node 483 (TableTree.node 482 (TableTree.leaf ([41])) (TableTree.leaf ([41]))) (TableTree.node 484 (TableTree.leaf ([68])) (TableTree.leaf ([41]))))) (TableTree.node 489 (TableTree.node 487 (TableTree.node 486 (TableTree.leaf ([44])) (TableTree.leaf ([44]))) (TableTree.node 488 (TableTree.leaf ([44])) (TableTree.leaf ([44])))) (TableTree.node 491 (TableTree.node 490 (TableTree.leaf ([68])) (TableTree.leaf ([41]))) (TableTree.node 492 (TableTree.leaf ([68])) (TableTree.leaf ([41]))))))) (TableTree.node 507 (TableTree.node 500 (TableTree.node 496 (TableTree.node 494 (TableTree.leaf ([41])) (TableTree.node 495 (TableTree.leaf ([41])) (TableTree.leaf ([41])))) (TableTree.node 498 (TableTree.node 497 (TableTree.leaf ([41])) (TableTree.leaf ([44]))) (TableTree.node 499 (TableTree.leaf ([44])) (TableTree.leaf ([42]))))) (TableTree.node 503 (TableTree.node 501 (TableTree.leaf ([42])) (TableTree.node 502 (TableTree.leaf ([44])) (TableTree.leaf ([42])))) (TableTree.node 505 (TableTree.node 504 (TableTree.leaf ([42])) (TableTree.leaf ([42]))) (TableTree.node 506 (TableTree.leaf ([43])) (TableTree.leaf ([43])))))) (TableTree.node 514 (TableTree.node 510 (TableTree.node 508 (TableTree.leaf ([42])) (TableTree.node 509 (TableTree.leaf ([43])) (TableTree.leaf ([44])))) (TableTree.node 512 (TableTree.node 511 (TableTree.leaf ([44])) (TableTree.leaf ([44]))) (TableTree.node 513 (TableTree.leaf ([44])) (TableTree.leaf ([44]))))) (TableTree.node 518 (TableTree.node 516 (TableTree.node 515 (TableTree.leaf ([44])) (TableTree.leaf ([42]))) (TableTree.node 517 (TableTree.leaf ([44])) (TableTree.leaf ([42])))) (TableTree.node 520 (TableTree.node 519 (TableTree.leaf ([43])) (TableTree.leaf ([42]))) (TableTree.node 521 (TableTree.leaf ([43])) (TableTree.leaf ([44])))))))) (TableTree.node 551 (TableTree.node 536 (TableTree.node 529 (TableTree.node 525 (TableTree.node 523 (TableTree.leaf ([44])) (TableTree.node 524 (TableTree.leaf ([42])) (TableTree.leaf ([42])))) (TableTree.node 527 (TableTree.node 526 (TableTree.leaf ([43])) (TableTree.leaf ([68]))) (TableTree.node 528 (TableTree.leaf ([44])) (TableTree.leaf ([42]))))) (TableTree.node 532 (TableTree.node 530 (TableTree.leaf ([44])) (TableTree.node 531 (TableTree.leaf ([42])) (TableTree.leaf ([43])))) (TableTree.node 534 (TableTree.node 533 (TableTree.leaf ([44])) (TableTree.leaf ([42]))) (TableTree.node 535 (TableTree.leaf ([44])) (TableTree.leaf ([42])))))) (TableTree.node 543 (TableTree.node 539 (TableTree.node 537 (TableTree.leaf ([42])) (TableTree.node 538 (TableTree.leaf ([43])) (TableTree.leaf ([42])))) (TableTree.node 541 (TableTree.node 540 (TableTree.leaf ([42])) (TableTree.leaf ([43]))) (TableTree.node 542 (TableTree.leaf ([43])) (TableTree.leaf ([44]))))) (TableTree.node 547 (TableTree.node 545 (TableTree.node 544 (TableTree.leaf ([44])) (TableTree.leaf ([42]))) (TableTree.node 546 (TableTree.leaf ([43])) (TableTree.leaf ([68])))) (TableTree.node 549 (TableTree.node 548 (TableTree.leaf ([41])) (TableTree.leaf ([41]))) (TableTree.node 550 (TableTree.leaf ([41])) (TableTree.leaf ([41]))))))) (TableTree.node 565 (TableTree.node 558 (TableTree.node 554 (TableTree.node 552 (TableTree.leaf ([41])) (TableTree.node 553 (TableTree.leaf ([44])) (TableTree.leaf ([42])))) (TableTree.node 556 (TableTree.node 555 (TableTree.leaf ([43])) (TableTree.leaf ([43]))) (TableTree.node 557 (TableTree.leaf ([44])) (TableTree.leaf ([44]))))) (TableTree.node 561 (TableTree.node 559 (TableTree.leaf ([42])) (TableTree.node 560 (TableTree.leaf ([42])) (TableTree.leaf ([44])))) (TableTree.node 563 (TableTree.node 562 (TableTree.leaf ([44])) (TableTree.leaf ([44]))) (TableTree.node 564 (TableTree.leaf ([44])) (TableTree.leaf ([42])))))) (TableTree.node 572 (TableTree.node 568 (TableTree.node 566 (TableTree.leaf ([42])) (TableTree.node 567 (TableTree.leaf ([44])) (TableTree.leaf ([44])))) (TableTree.node 570 (TableTree.node 569 (TableTree.leaf ([42])) (TableTree.leaf ([43]))) (TableTree.node 571 (TableTree.leaf ([68])) (TableTree.leaf ([41]))))) (TableTree.node 576 (TableTree.node 574 (TableTree.node 573 (TableTree.leaf ([44])) (TableTree.leaf ([44]))) (TableTree.node 575 (TableTree.leaf ([44])) (TableTree.leaf ([42])))) (TableTree.node 578 (TableTree.node 577 (TableTree.leaf ([44])) (TableTree.leaf ([44]))) (TableTree.node 579 (TableTree.leaf ([44])) (TableTree.leaf ([44]))))))))) (TableTree.node 638 (TableTree.node 609 (TableTree.node 594 (TableTree.node 587 (TableTree.node 583 (TableTree.node 581 (TableTree.leaf ([42])) (TableTree.node 582 (TableTree.leaf ([44])) (TableTree.leaf ([42])))) (TableTree.node 585 (TableTree.node 584 (TableTree.leaf ([44])) (TableTree.leaf ([44]))) (TableTree.node 586 (TableTree.leaf ([42])) (TableTree.leaf ([43]))))) (TableTree.node 590 (TableTree.node 588 (TableTree.leaf ([43])) (TableTree.node 589 (TableTree.leaf ([42])) (TableTree.leaf ([43])))) (TableTree.node 592 (TableTree.node 591 (TableTree.leaf ([68])) (TableTree.leaf ([44]))) (TableTree.node 593 (TableTree.leaf ([42])) (TableTree.leaf ([42])))))) (TableTree.node 601 (TableTree.node 597 (TableTree.node 595 (TableTree.leaf ([43])) (TableTree.node 596 (TableTree.leaf ([44])) (TableTree.leaf ([42])))) (TableTree.node 599 (TableTree.node 598 (TableTree.leaf ([44])) (TableTree.leaf ([44]))) (TableTree.node 600 (TableTree.leaf ([44])) (TableTree.leaf ([44]))))) (TableTree.node 605 (TableTree.node 603 (TableTree.node 602 (TableTree.leaf ([42])) (TableTree.leaf ([43]))) (TableTree.node 604 (TableTree.leaf ([44])) (TableTree.leaf ([44])))) (TableTree.node 607 (TableTree.node 606 (TableTree.leaf ([44])) (TableTree.leaf ([44]))) (TableTree.node 608 (TableTree.leaf ([44])) (TableTree.leaf ([42]))))))) (TableTree.node 623 (TableTree.node 616 (TableTree.node 612 (TableTree.node 610 (TableTree.leaf ([43])) (TableTree.node 611 (TableTree.leaf ([43])) (TableTree.leaf ([44])))) (TableTree.node 614 (TableTree.node 613 (TableTree.leaf ([42])) (TableTree.leaf ([44]))) (TableTree.node 615 (TableTree.leaf ([44])) (TableTree.leaf ([42]))))) (TableTree.node 619 (TableTree.node 617 (TableTree.leaf ([44])) (TableTree.node 618 (TableTree.leaf ([44])) (TableTree.leaf ([42])))) (TableTree.node 621 (TableTree.node 620 (TableTree.leaf ([44])) (TableTree.leaf ([44]))) (TableTree.node 622 (TableTree.leaf ([44])) (TableTree.leaf ([44])))))) (TableTree.node 630 (TableTree.node 626 (TableTree.node 624 (TableTree.leaf ([41])) (TableTree.node 625 (TableTree.leaf ([41])) (TableTree.leaf ([41])))) (TableTree.node 628 (TableTree.node 627 (TableTree.leaf ([41])) (TableTree.leaf ([41]))) (TableTree.node 629 (TableTree.leaf ([41])) (TableTree.leaf ([41]))))) (TableTree.node 634 (TableTree.node 632 (TableTree.node 631 (TableTree.leaf ([41])) (TableTree.leaf ([43]))) (TableTree.node 633 (TableTree.leaf ([43])) (TableTree.leaf ([44])))) (TableTree.node 636 (TableTree.node 635 (TableTree.leaf ([42])) (TableTree.leaf ([44]))) (TableTree.node 637 (TableTree.leaf ([42])) (TableTree.leaf ([42])))))))) (TableTree.node 667 (TableTree.node 652 (TableTree.node 645 (TableTree.node 641 (TableTree.node 639 (TableTree.leaf ([44])) (TableTree.node 640 (TableTree.leaf ([44])) (TableTree.leaf ([42])))) (TableTree.node 643 (TableTree.node 642 (TableTree.leaf ([44])) (TableTree.leaf ([42]))) (TableTree.node 644 (TableTree.leaf ([42])) (TableTree.leaf ([43]))))) (TableTree.node 648 (TableTree.node 646 (TableTree.leaf ([43])) (TableTree.node 647 (TableTree.leaf ([42])) (TableTree.leaf ([43])))) (TableTree.node 650 (TableTree.node 649 (TableTree.leaf ([68])) (TableTree.leaf ([68]))) (TableTree.node 651 (TableTree.leaf ([41])) (TableTree.leaf ([41])))))) (TableTree.node 659 (TableTree.node 655 (TableTree.node 653 (TableTree.leaf ([68])) (TableTree.node 654 (TableTree.leaf ([41])) (TableTree.leaf ([44])))) (TableTree.node 657 (TableTree.node 656 (TableTree.leaf ([44])) (TableTree.leaf ([44]))) (TableTree.node 658 (TableTree.leaf ([44])) (TableTree.leaf ([44]))))) (TableTree.node 663 (TableTree.node 661 (TableTree.node 660 (TableTree.leaf ([44])) (TableTree.leaf ([42]))) (TableTree.node 662 (TableTree.leaf ([42])) (TableTree.leaf ([44])))) (TableTree.node 665 (TableTree.node 664 (TableTree.leaf ([42])) (TableTree.leaf ([42]))) (TableTree.node 666 (TableTree.leaf ([42])) (TableTree.leaf ([43]))))))) (TableTree.node 681 (TableTree.node 674 (TableTree.node 670 (TableTree.node 668 (TableTree.leaf ([43])) (TableTree.node 669 (TableTree.leaf ([42])) (TableTree.leaf ([43])))) (TableTree.node 672 (TableTree.node 671 (TableTree.leaf ([44])) (TableTree.leaf ([44]))) (TableTree.node 673 (TableTree.leaf ([44])) (TableTree.leaf ([44]))))) (TableTree.node 677 (TableTree.node 675 (TableTree.leaf ([44])) (TableTree.node 676 (TableTree.leaf ([44])) (TableTree.leaf ([42])))) (TableTree.node 679 (TableTree.node 678 (TableTree.leaf ([44])) (TableTree.leaf ([42]))) (TableTree.node 680 (TableTree.leaf ([43])) (TableTree.leaf ([42])))))) (TableTree.node 688 (TableTree.node 684 (TableTree.node 682 (TableTree.leaf ([43])) (TableTree.node 683 (TableTree.leaf ([44])) (TableTree.leaf ([42])))) (TableTree.node 686 (TableTree.node 685 (TableTree.leaf ([44])) (TableTree.leaf ([44]))) (TableTree.node 687 (TableTree.leaf ([44])) (TableTree.leaf ([42]))))) (TableTree.node 692 (TableTree.node 690 (TableTree.node 689 (TableTree.leaf ([44])) (TableTree.leaf ([44]))) (TableTree.node 691 (TableTree.leaf ([42])) (TableTree.leaf ([43])))) (TableTree.node 694 (TableTree.node 693 (TableTree.leaf ([44])) (TableTree.leaf ([44]))) (TableTree.node 695 (TableTree.leaf ([44])) (TableTree.leaf ([42])))))))))) (TableTree.node 812 (TableTree.node 754 (TableTree.node 725 (TableTree.node 710 (TableTree.node 703 (TableTree.node 699 (TableTree.node 697 (TableTree.leaf ([44])) (TableTree.node 698 (TableTree.leaf ([42])) (TableTree.leaf ([44])))) (TableTree.node 701 (TableTree.node 700 (TableTree.leaf ([42])) (TableTree.leaf ([42]))) (TableTree.node 702 (TableTree.leaf ([43])) (TableTree.leaf ([44]))))) (TableTree.node 706 (TableTree.node 704 (TableTree.leaf ([44])) (TableTree.node 705 (TableTree.leaf ([44])) (TableTree.leaf ([42])))) (TableTree.node 708 (TableTree.node 707 (TableTree.leaf ([43])) (TableTree.leaf ([43]))) (TableTree.node 709 (TableTree.leaf ([42])) (TableTree.leaf ([43])))))) (TableTree.node 717 (TableTree.node 713 (TableTree.node 711 (TableTree.leaf ([68])) (TableTree.node 712 (TableTree.leaf ([44])) (TableTree.leaf ([43])))) (TableTree.node 715 (TableTree.node 714 (TableTree.leaf ([42])) (TableTree.leaf ([43]))) (TableTree.node 716 (TableTree.leaf ([68])) (TableTree.leaf ([41]))))) (TableTree.node 721 (TableTree.node 719 (TableTree.node 718 (TableTree.leaf ([41])) (TableTree.leaf ([41]))) (TableTree.node 720 (TableTree.leaf ([41])) (TableTree.leaf ([41])))) (TableTree.node 723 (TableTree.node 722 (TableTree.leaf ([44])) (TableTree.leaf ([41]))) (TableTree.node 724 (TableTree.leaf ([41])) (TableTree.leaf ([41]))))))) (TableTree.node 739 (TableTree.node 732 (TableTree.node 728 (TableTree.node 726 (TableTree.leaf ([44])) (TableTree.node 727 (TableTree.leaf ([44])) (TableTree.leaf ([68])))) (TableTree.node 730 (TableTree.node 729 (TableTree.leaf ([68])) (TableTree.leaf ([41]))) (TableTree.node 731 (TableTree.leaf ([41])) (TableTree.leaf ([68]))))) (TableTree.node 735 (TableTree.node 733 (TableTree.leaf ([41])) (TableTree.node 734 (TableTree.leaf ([44])) (TableTree.leaf ([42])))) (TableTree.node 737 (TableTree.node 736 (TableTree.leaf ([68])) (TableTree.leaf ([44]))) (TableTree.node 738 (TableTree.leaf ([42])) (TableTree.leaf ([43])))))) (TableTree.node 746 (TableTree.node 742 (TableTree.node 740 (TableTree.leaf ([43])) (TableTree.node 741 (TableTree.leaf ([44])) (TableTree.leaf ([42])))) (TableTree.node 744 (TableTree.node 743 (TableTree.leaf ([43])) (TableTree.leaf ([42]))) (TableTree.node 745 (TableTree.leaf ([44])) (TableTree.leaf ([42]))))) (TableTree.node 750 (TableTree.node 748 (TableTree.node 747 (TableTree.leaf ([44])) (TableTree.leaf ([43]))) (TableTree.node 749 (TableTree.leaf ([42])) (TableTree.leaf ([68])))) (TableTree.node 752 (TableTree.node 751 (TableTree.leaf ([42])) (TableTree.leaf ([43]))) (TableTree.node 753 (TableTree.leaf ([68])) (TableTree.leaf ([68])))))))) (TableTree.node 783 (TableTree.node 768 (TableTree.node 761 (TableTree.node 757 (TableTree.node 755 (TableTree.leaf ([41])) (TableTree.node 756 (TableTree.leaf ([41])) (TableTree.leaf ([68])))) (TableTree.node 759 (TableTree.node 758 (TableTree.leaf ([41])) (TableTree.leaf ([41]))) (TableTree.node 760 (TableTree.leaf ([41])) (TableTree.leaf ([41]))))) (TableTree.node 764 (TableTree.node 762 (TableTree.leaf ([41])) (TableTree.node 763 (TableTree.leaf ([41])) (TableTree.leaf ([41])))) (TableTree.node 766 (TableTree.node 765 (TableTree.leaf ([41])) (TableTree.leaf ([41]))) (TableTree.node 767 (TableTree.leaf ([41])) (TableTree.leaf ([41])))))) (TableTree.node 775 (TableTree.node 771 (TableTree.node 769 (TableTree.leaf ([41])) (TableTree.node 770 (TableTree.leaf ([41])) (TableTree.leaf ([44])))) (TableTree.node 773 (TableTree.node 772 (TableTree.leaf ([68])) (TableTree.leaf ([41]))) (TableTree.node 774 (TableTree.leaf ([42])) (TableTree.leaf ([43]))))) (TableTree.node 779 (TableTree.node 777 (TableTree.node 776 (TableTree.leaf ([68])) (TableTree.leaf ([43]))) (TableTree.node 778 (TableTree.leaf ([68])) (TableTree.leaf ([44])))) (TableTree.node 781 (TableTree.node 780 (TableTree.leaf ([44])) (TableTree.leaf ([42]))) (TableTree.node 782 (TableTree.leaf ([43])) (TableTree.leaf ([68]))))))) (TableTree.node 797 (TableTree.node 790 (TableTree.node 786 (TableTree.node 784 (TableTree.leaf ([68])) (TableTree.node 785 (TableTree.leaf ([41])) (TableTree.leaf ([41])))) (TableTree.node 788 (TableTree.node 787 (TableTree.leaf ([41])) (TableTree.leaf ([41]))) (TableTree.node 789 (TableTree.leaf ([41])) (TableTree.leaf ([41]))))) (TableTree.node 793 (TableTree.node 791 (TableTree.leaf ([41])) (TableTree.node 792 (TableTree.leaf ([41])) (TableTree.leaf ([41])))) (TableTree.node 795 (TableTree.node 794 (TableTree.leaf ([41])) (TableTree.leaf ([41]))) (TableTree.node 796 (TableTree.leaf ([42])) (TableTree.leaf ([43])))))) (TableTree.node 804 (TableTree.node 800 (TableTree.node 798 (TableTree.leaf ([68])) (TableTree.node 799 (TableTree.leaf ([43])) (TableTree.leaf ([44])))) (TableTree.node 802 (TableTree.node 801 (TableTree.leaf ([44])) (TableTree.leaf ([42]))) (TableTree.node 803 (TableTree.leaf ([41])) (TableTree.leaf ([41]))))) (TableTree.node 808 (TableTree.node 806 (TableTree.node 805 (TableTree.leaf ([41])) (TableTree.leaf ([41]))) (TableTree.node 807 (TableTree.leaf ([41])) (TableTree.leaf ([41])))) (TableTree.node 810 (TableTree.node 809 (TableTree.leaf ([68])) (TableTree.leaf ([41]))) (TableTree.node 811 (TableTree.leaf ([41])) (TableTree.leaf ([41]))))))))) (TableTree.node 870 (TableTree.node 841 (TableTree.node 826 (TableTree.node 819 (TableTree.node 815 (TableTree.node 813 (TableTree.leaf ([72])) (TableTree.node 814 (TableTree.leaf ([72])) (TableTree.leaf ([72])))) (TableTree.node 817 (TableTree.node 816 (TableTree.leaf ([72])) (TableTree.leaf ([72]))) (TableTree.node 818 (TableTree.leaf ([72])) (TableTree.leaf ([72]))))) (TableTree.node 822 (TableTree.node 820 (TableTree.leaf ([72])) (TableTree.node 821 (TableTree.leaf ([72])) (TableTree.leaf ([42,72])))) (TableTree.node 824 (TableTree.node 823 (TableTree.leaf ([42,72])) (TableTree.leaf ([44,72]))) (TableTree.node 825 (TableTree.leaf ([44,72])) (TableTree.leaf ([44,72])))))) (TableTree.node 833 (TableTree.node 829 (TableTree.node 827 (TableTree.leaf ([42,72])) (TableTree.node 828 (TableTree.leaf ([44,72])) (TableTree.leaf ([44,72])))) (TableTree.node 831 (TableTree.node 830 (TableTree.leaf ([42,72])) (TableTree.leaf ([42,72]))) (TableTree.node 832 (TableTree.leaf ([44,72])) (TableTree.leaf ([44,72]))))) (TableTree.node 837 (TableTree.node 835 (TableTree.node 834 (TableTree.leaf ([44,72])) (TableTree.leaf ([44,72]))) (TableTree.node 836 (TableTree.leaf ([42,72])) (TableTree.leaf ([42,72])))) (TableTree.node 839 (TableTree.node 838 (TableTree.leaf ([44,72])) (TableTree.leaf ([44,72]))) (TableTree.node 840 (TableTree.leaf ([42,72])) (TableTree.leaf ([44,72]))))))) (TableTree.node 855 (TableTree.node 848 (TableTree.node 844 (TableTree.node 842 (TableTree.leaf ([44,72])) (TableTree.node 843 (TableTree.leaf ([44,72])) (TableTree.leaf ([42,72])))) (TableTree.node 846 (TableTree.node 845 (TableTree.leaf ([44,72])) (TableTree.leaf ([44,72]))) (TableTree.node 847 (TableTree.leaf ([44,72])) (TableTree.leaf ([44,72]))))) (TableTree.node 851 (TableTree.node 849 (TableTree.leaf ([44,72])) (TableTree.node 850 (TableTree.leaf ([44,72])) (TableTree.leaf ([42,72])))) (TableTree.node 853 (TableTree.node 852 (TableTree.leaf ([44,72])) (TableTree.leaf ([42,72]))) (TableTree.node 854 (TableTree.leaf ([44,72])) (TableTree.leaf ([44,72])))))) (TableTree.node 862 (TableTree.node 858 (TableTree.node 856 (TableTree.leaf ([44,72])) (TableTree.node 857 (TableTree.leaf ([42,72])) (TableTree.leaf ([44,72])))) (TableTree.node 860 (TableTree.node 859 (TableTree.leaf ([42,72])) (TableTree.leaf ([44,72]))) (TableTree.node 861 (TableTree.leaf ([42,72])) (TableTree.leaf ([42,72]))))) (TableTree.node 866 (TableTree.node 864 (TableTree.node 863 (TableTree.leaf ([44,72])) (TableTree.leaf ([44,72]))) (TableTree.node 865 (TableTree.leaf ([44,72])) (TableTree.leaf ([42,72])))) (TableTree.node 868 (TableTree.node 867 (TableTree.leaf ([44,72])) (TableTree.leaf ([42,72]))) (TableTree.node 869 (TableTree.leaf ([42,72])) (TableTree.leaf ([44,72])))))))) (TableTree.node 899 (TableTree.node 884 (TableTree.node 877 (TableTree.node 873 (TableTree.node 871 (TableTree.leaf ([44,72])) (TableTree.node 872 (TableTree.leaf ([42,72])) (TableTree.leaf ([44,72])))) (TableTree.node 875 (TableTree.node 874 (TableTree.leaf ([42,72])) (TableTree.leaf ([44,72]))) (TableTree.node 876 (TableTree.leaf ([42,72])) (TableTree.leaf ([42,72]))))) (TableTree.node 880 (TableTree.node 878 (TableTree.leaf ([44,72])) (TableTree.node 879 (TableTree.leaf ([42,72])) (TableTree.leaf ([44,72])))) (TableTree.node 882 (TableTree.node 881 (TableTree.leaf ([42,72])) (TableTree.leaf ([42,72]))) (TableTree.node 883 (TableTree.leaf ([44,72])) (TableTree.leaf ([44,72])))))) (TableTree.node 891 (TableTree.node 887 (TableTree.node 885 (TableTree.leaf ([42,72])) (TableTree.node 886 (TableTree.leaf ([42,44,72])) (TableTree.leaf ([42,44,72])))) (TableTree.node 889 (TableTree.node 888 (TableTree.leaf ([42,44,72])) (TableTree.leaf ([42,44,72]))) (TableTree.node 890 (TableTree.leaf ([42,44,72])) (TableTree.leaf ([42,44,72]))))) (TableTree.node 895 (TableTree.node 893 (TableTree.node 892 (TableTree.leaf ([42,44,72])) (TableTree.leaf ([42,44,72]))) (TableTree.node 894 (TableTree.leaf ([42,44,72])) (TableTree.leaf ([42,44,72])))) (TableTree.node 897 (TableTree.node 896 (TableTree.leaf ([42,44,72])) (TableTree.leaf ([42,44,72]))) (TableTree.node 898 (TableTree.leaf ([42,44,72])) (TableTree.leaf ([42,44,72]))))))) (TableTree.node 914 (TableTree.node 906 (TableTree.node 902 (TableTree.node 900 (TableTree.leaf ([42,44,72])) (TableTree.node 901 (TableTree.leaf ([42,44,72])) (TableTree.leaf ([42,44,72])))) (TableTree.node 904 (TableTree.node 903 (TableTree.leaf ([42,44,72])) (TableTree.leaf ([42,44,72]))) (TableTree.node 905 (TableTree.leaf ([42,44,72])) (TableTree.leaf ([42,44,72]))))) (TableTree.node 910 (TableTree.node 908 (TableTree.node 907 (TableTree.leaf ([42,44,72])) (TableTree.leaf ([42,44,72]))) (TableTree.node 909 (TableTree.leaf ([42,44,72])) (TableTree.leaf ([42,44,72])))) (TableTree.node 912 (TableTree.node 911 (TableTree.leaf ([42,44,72])) (TableTree.leaf ([42,44,72]))) (TableTree.node 913 (TableTree.leaf ([42,44,72])) (TableTree.leaf ([42,44,72])))))) (TableTree.node 921 (TableTree.node 917 (TableTree.node 915 (TableTree.leaf ([42,44,72])) (TableTree.node 916 (TableTree.leaf ([42,44,72])) (TableTree.leaf ([42,44,72])))) (TableTree.node 919 (TableTree.node 918 (TableTree.leaf ([42,44,72])) (TableTree.leaf ([42,44,72]))) (TableTree.node 920 (TableTree.leaf ([42,44,72])) (TableTree.leaf ([42,44,72]))))) (TableTree.node 925 (TableTree.node 923 (TableTree.node 922 (TableTree.leaf ([42,44,72])) (TableTree.leaf ([42,44,72]))) (TableTree.node 924 (TableTree.leaf ([42,44,72])) (TableTree.leaf ([42,44,72])))) (TableTree.node 927 (TableTree.node 926 (TableTree.leaf ([42,44,72])) (TableTree.leaf ([42,44,72]))) (TableTree.node 928 (TableTree.leaf ([42,44,72])) (TableTree.leaf ([42,44,72]))))))))))))
private def endAt (i : ℕ) : (List ℕ) := if i < 929 then TableTree.lookup endAtTree i else []
private def hAtTree : TableTree ((Array (ℤ))) := (TableTree.node 464 (TableTree.node 232 (TableTree.node 116 (TableTree.node 58 (TableTree.node 29 (TableTree.node 14 (TableTree.node 7 (TableTree.node 3 (TableTree.node 1 (TableTree.leaf (#[0,0,0])) (TableTree.node 2 (TableTree.leaf (#[2901000,2901000,2901000])) (TableTree.leaf (#[4344599,4344599,4344599])))) (TableTree.node 5 (TableTree.node 4 (TableTree.leaf (#[5802000,5802000,5802000])) (TableTree.leaf (#[5802599,5802599,5802599]))) (TableTree.node 6 (TableTree.leaf (#[6358198,6358198,6358198])) (TableTree.leaf (#[6802797,6802797,6802797]))))) (TableTree.node 10 (TableTree.node 8 (TableTree.leaf (#[7246797,7246797,7246797])) (TableTree.node 9 (TableTree.leaf (#[7580396,7580396,7580396])) (TableTree.leaf (#[5900995,5900995,5900995])))) (TableTree.node 12 (TableTree.node 11 (TableTree.leaf (#[5900995,5900995,5900995])) (TableTree.leaf (#[5456995,5456995,5456995]))) (TableTree.node 13 (TableTree.leaf (#[5901594,5901594,5901594])) (TableTree.leaf (#[5901594,5901594,5901594])))))) (TableTree.node 21 (TableTree.node 17 (TableTree.node 15 (TableTree.leaf (#[6123594,6123594,6123594])) (TableTree.node 16 (TableTree.leaf (#[6346193,6346193,6346193])) (TableTree.leaf (#[6457193,6457193,6457193])))) (TableTree.node 19 (TableTree.node 18 (TableTree.leaf (#[6679193,6679193,6679193])) (TableTree.leaf (#[5347193,5347193,5347193]))) (TableTree.node 20 (TableTree.leaf (#[5458193,5458193,5458193])) (TableTree.leaf (#[5680193,5680193,5680193]))))) (TableTree.node 25 (TableTree.node 23 (TableTree.node 22 (TableTree.leaf (#[5791193,5791193,5791193])) (TableTree.leaf (#[5902193,5902193,5902193]))) (TableTree.node 24 (TableTree.leaf (#[6013193,6013193,6013193])) (TableTree.leaf (#[6124792,6124792,6124792])))) (TableTree.node 27 (TableTree.node 26 (TableTree.leaf (#[6235792,6235792,6235792])) (TableTree.leaf (#[6346792,6346792,6346792]))) (TableTree.node 28 (TableTree.leaf (#[5999990,5999990,5999990])) (TableTree.leaf (#[5999996,5999996,5999996]))))))) (TableTree.node 43 (TableTree.node 36 (TableTree.node 32 (TableTree.node 30 (TableTree.leaf (#[5999990,5999990,5999990])) (TableTree.node 31 (TableTree.leaf (#[5905793,5905793,5905793])) (TableTree.leaf (#[5222990,5222990,5222990])))) (TableTree.node 34 (TableTree.node 33 (TableTree.leaf (#[5222996,5222996,5222996])) (TableTree.leaf (#[5999990,5999990,5999990]))) (TableTree.node 35 (TableTree.leaf (#[5905792,5905792,5905792])) (TableTree.leaf (#[5999990,5999990,5999990]))))) (TableTree.node 39 (TableTree.node 37 (TableTree.leaf (#[5999992,5999992,5999992])) (TableTree.node 38 (TableTree.leaf (#[5444990,5444990,5444990])) (TableTree.leaf (#[5350793,5350793,5350793])))) (TableTree.node 41 (TableTree.node 40 (TableTree.leaf (#[5555990,5555990,5555990])) (TableTree.leaf (#[5555996,5555996,5555996]))) (TableTree.node 42 (TableTree.leaf (#[5555990,5555990,5555990])) (TableTree.leaf (#[5461793,5461793,5461793])))))) (TableTree.node 50 (TableTree.node 46 (TableTree.node 44 (TableTree.leaf (#[5666990,5666990,5666990])) (TableTree.node 45 (TableTree.leaf (#[5666996,5666996,5666996])) (TableTree.leaf (#[5999990,5999990,5999990])))) (TableTree.node 48 (TableTree.node 47 (TableTree.leaf (#[5999990,5999990,5999990])) (TableTree.leaf (#[5888990,5888990,5888990]))) (TableTree.node 49 (TableTree.leaf (#[5999990,5999990,5999990])) (TableTree.leaf (#[5999990,5999990,5999990]))))) (TableTree.node 54 (TableTree.node 52 (TableTree.node 51 (TableTree.leaf (#[6110990,6110990,6110990])) (TableTree.leaf (#[6110990,6110990,6110990]))) (TableTree.node 53 (TableTree.leaf (#[6221990,6221990,6221990])) (TableTree.leaf (#[6332990,6332990,6332990])))) (TableTree.node 56 (TableTree.node 55 (TableTree.leaf (#[5777995,5777995,5777995])) (TableTree.leaf (#[5777990,5777990,5777990]))) (TableTree.node 57 (TableTree.leaf (#[5794792,5794792,5794792])) (TableTree.leaf (#[5888990,5888990,5888990])))))))) (TableTree.node 87 (TableTree.node 72 (TableTree.node 65 (TableTree.node 61 (TableTree.node 59 (TableTree.leaf (#[5888995,5888995,5888995])) (TableTree.node 60 (TableTree.leaf (#[5888990,5888990,5888990])) (TableTree.leaf (#[5905792,5905792,5905792])))) (TableTree.node 63 (TableTree.node 62 (TableTree.leaf (#[5999990,5999990,5999990])) (TableTree.leaf (#[5999992,5999992,5999992]))) (TableTree.node 64 (TableTree.leaf (#[5999990,5999990,5999990])) (TableTree.leaf (#[6016793,6016793,6016793]))))) (TableTree.node 68 (TableTree.node 66 (TableTree.leaf (#[6110990,6110990,6110990])) (TableTree.node 67 (TableTree.leaf (#[6110997,6110997,6110997])) (TableTree.leaf (#[6110990,6110990,6110990])))) (TableTree.node 70 (TableTree.node 69 (TableTree.leaf (#[6127794,6127794,6127794])) (TableTree.leaf (#[6221990,6221990,6221990]))) (TableTree.node 71 (TableTree.leaf (#[6221997,6221997,6221997])) (TableTree.leaf (#[6221990,6221990,6221990])))))) (TableTree.node 79 (TableTree.node 75 (TableTree.node 73 (TableTree.leaf (#[5888990,5888990,5888990])) (TableTree.node 74 (TableTree.leaf (#[5888990,5888990,5888990])) (TableTree.leaf (#[5888996,5888996,5888996])))) (TableTree.node 77 (TableTree.node 76 (TableTree.leaf (#[5888999,5888999,5888999])) (TableTree.leaf (#[5888990,5888990,5888990]))) (TableTree.node 78 (TableTree.leaf (#[5999990,5999990,5999990])) (TableTree.leaf (#[5794793,5794793,5794793]))))) (TableTree.node 83 (TableTree.node 81 (TableTree.node 80 (TableTree.leaf (#[5999996,5999996,5999996])) (TableTree.leaf (#[5999990,5999990,5999990]))) (TableTree.node 82 (TableTree.leaf (#[6110990,6110990,6110990])) (TableTree.leaf (#[5999999,5999999,5999999])))) (TableTree.node 85 (TableTree.node 84 (TableTree.leaf (#[6110998,6110998,6110998])) (TableTree.leaf (#[6110990,6110990,6110990]))) (TableTree.node 86 (TableTree.leaf (#[6221990,6221990,6221990])) (TableTree.leaf (#[6016792,6016792,6016792]))))))) (TableTree.node 101 (TableTree.node 94 (TableTree.node 90 (TableTree.node 88 (TableTree.leaf (#[6127793,6127793,6127793])) (TableTree.node 89 (TableTree.leaf (#[6221990,6221990,6221990])) (TableTree.leaf (#[5777990,5777990,5777990])))) (TableTree.node 92 (TableTree.node 91 (TableTree.leaf (#[5777990,5777990,5777990])) (TableTree.leaf (#[6221996,6221996,6221996]))) (TableTree.node 93 (TableTree.leaf (#[5777994,5777994,5777994])) (TableTree.leaf (#[5794787,5794787,5794787]))))) (TableTree.node 97 (TableTree.node 95 (TableTree.leaf (#[5888990,5888990,5888990])) (TableTree.node 96 (TableTree.leaf (#[5794790,5794790,5794790])) (TableTree.leaf (#[5888990,5888990,5888990])))) (TableTree.node 99 (TableTree.node 98 (TableTree.leaf (#[5794793,5794793,5794793])) (TableTree.leaf (#[5888996,5888996,5888996]))) (TableTree.node 100 (TableTree.leaf (#[5905787,5905787,5905787])) (TableTree.leaf (#[5999990,5999990,5999990])))))) (TableTree.node 108 (TableTree.node 104 (TableTree.node 102 (TableTree.leaf (#[5905793,5905793,5905793])) (TableTree.node 103 (TableTree.leaf (#[5999990,5999990,5999990])) (TableTree.leaf (#[5999996,5999996,5999996])))) (TableTree.node 106 (TableTree.node 105 (TableTree.leaf (#[5999999,5999999,5999999])) (TableTree.leaf (#[5905789,5905789,5905789]))) (TableTree.node 107 (TableTree.leaf (#[5999990,5999990,5999990])) (TableTree.leaf (#[6110993,6110993,6110993]))))) (TableTree.node 112 (TableTree.node 110 (TableTree.node 109 (TableTree.leaf (#[6110990,6110990,6110990])) (TableTree.leaf (#[5905793,5905793,5905793]))) (TableTree.node 111 (TableTree.leaf (#[6110996,6110996,6110996])) (TableTree.leaf (#[6016790,6016790,6016790])))) (TableTree.node 114 (TableTree.node 113 (TableTree.leaf (#[6110990,6110990,6110990])) (TableTree.leaf (#[6016796,6016796,6016796]))) (TableTree.node 115 (TableTree.leaf (#[6110990,6110990,6110990])) (TableTree.leaf (#[6110999,6110999,6110999]))))))))) (TableTree.node 174 (TableTree.node 145 (TableTree.node 130 (TableTree.node 123 (TableTree.node 119 (TableTree.node 117 (TableTree.leaf (#[6110998,6110998,6110998])) (TableTree.node 118 (TableTree.leaf (#[5888990,5888990,5888990])) (TableTree.leaf (#[5888990,5888990,5888990])))) (TableTree.node 121 (TableTree.node 120 (TableTree.leaf (#[5888990,5888990,5888990])) (TableTree.leaf (#[5999990,5999990,5999990]))) (TableTree.node 122 (TableTree.leaf (#[5999990,5999990,5999990])) (TableTree.leaf (#[5999990,5999990,5999990]))))) (TableTree.node 126 (TableTree.node 124 (TableTree.leaf (#[6110990,6110990,6110990])) (TableTree.node 125 (TableTree.leaf (#[6110990,6110990,6110990])) (TableTree.leaf (#[6110990,6110990,6110990])))) (TableTree.node 128 (TableTree.node 127 (TableTree.leaf (#[5000990,5000990,5000990])) (TableTree.leaf (#[5000990,5000990,5000990]))) (TableTree.node 129 (TableTree.leaf (#[4906787,4906787,4906787])) (TableTree.leaf (#[5000990,5000990,5000990])))))) (TableTree.node 137 (TableTree.node 133 (TableTree.node 131 (TableTree.leaf (#[4906790,4906790,4906790])) (TableTree.node 132 (TableTree.leaf (#[5000990,5000990,5000990])) (TableTree.leaf (#[4906787,4906787,4906787])))) (TableTree.node 135 (TableTree.node 134 (TableTree.leaf (#[5000990,5000990,5000990])) (TableTree.leaf (#[5017793,5017793,5017793]))) (TableTree.node 136 (TableTree.leaf (#[5111990,5111990,5111990])) (TableTree.leaf (#[5017789,5017789,5017789]))))) (TableTree.node 141 (TableTree.node 139 (TableTree.node 138 (TableTree.leaf (#[5111990,5111990,5111990])) (TableTree.leaf (#[5111993,5111993,5111993]))) (TableTree.node 140 (TableTree.leaf (#[5111990,5111990,5111990])) (TableTree.leaf (#[5128790,5128790,5128790])))) (TableTree.node 143 (TableTree.node 142 (TableTree.leaf (#[5222990,5222990,5222990])) (TableTree.leaf (#[5128796,5128796,5128796]))) (TableTree.node 144 (TableTree.leaf (#[5222990,5222990,5222990])) (TableTree.leaf (#[5222993,5222993,5222993]))))))) (TableTree.node 159 (TableTree.node 152 (TableTree.node 148 (TableTree.node 146 (TableTree.leaf (#[5222996,5222996,5222996])) (TableTree.node 147 (TableTree.leaf (#[5222990,5222990,5222990])) (TableTree.leaf (#[5222990,5222990,5222990])))) (TableTree.node 150 (TableTree.node 149 (TableTree.leaf (#[5239790,5239790,5239790])) (TableTree.leaf (#[5333993,5333993,5333993]))) (TableTree.node 151 (TableTree.leaf (#[5333990,5333990,5333990])) (TableTree.leaf (#[5333990,5333990,5333990]))))) (TableTree.node 155 (TableTree.node 153 (TableTree.leaf (#[5333996,5333996,5333996])) (TableTree.node 154 (TableTree.leaf (#[5333995,5333995,5333995])) (TableTree.leaf (#[5333990,5333990,5333990])))) (TableTree.node 157 (TableTree.node 156 (TableTree.leaf (#[5333990,5333990,5333990])) (TableTree.leaf (#[5350790,5350790,5350790]))) (TableTree.node 158 (TableTree.leaf (#[5350791,5350791,5350791])) (TableTree.leaf (#[5444990,5444990,5444990])))))) (TableTree.node 166 (TableTree.node 162 (TableTree.node 160 (TableTree.leaf (#[5444990,5444990,5444990])) (TableTree.node 161 (TableTree.leaf (#[5444994,5444994,5444994])) (TableTree.leaf (#[5999994,5999994,5999994])))) (TableTree.node 164 (TableTree.node 163 (TableTree.leaf (#[5444990,5444990,5444990])) (TableTree.leaf (#[5999990,5999990,5999990]))) (TableTree.node 165 (TableTree.leaf (#[5999990,5999990,5999990])) (TableTree.leaf (#[5905793,5905793,5905793]))))) (TableTree.node 170 (TableTree.node 168 (TableTree.node 167 (TableTree.leaf (#[5999996,5999996,5999996])) (TableTree.leaf (#[5905787,5905787,5905787]))) (TableTree.node 169 (TableTree.leaf (#[5999990,5999990,5999990])) (TableTree.leaf (#[5905790,5905790,5905790])))) (TableTree.node 172 (TableTree.node 171 (TableTree.leaf (#[5999990,5999990,5999990])) (TableTree.leaf (#[5999996,5999996,5999996]))) (TableTree.node 173 (TableTree.leaf (#[5999999,5999999,5999999])) (TableTree.leaf (#[5905787,5905787,5905787])))))))) (TableTree.node 203 (TableTree.node 188 (TableTree.node 181 (TableTree.node 177 (TableTree.node 175 (TableTree.leaf (#[5999990,5999990,5999990])) (TableTree.node 176 (TableTree.leaf (#[5905793,5905793,5905793])) (TableTree.leaf (#[5999990,5999990,5999990])))) (TableTree.node 179 (TableTree.node 178 (TableTree.leaf (#[6016793,6016793,6016793])) (TableTree.leaf (#[6110996,6110996,6110996]))) (TableTree.node 180 (TableTree.leaf (#[6016789,6016789,6016789])) (TableTree.leaf (#[6110990,6110990,6110990]))))) (TableTree.node 184 (TableTree.node 182 (TableTree.leaf (#[6110993,6110993,6110993])) (TableTree.node 183 (TableTree.leaf (#[6110990,6110990,6110990])) (TableTree.leaf (#[6110999,6110999,6110999])))) (TableTree.node 186 (TableTree.node 185 (TableTree.leaf (#[6110998,6110998,6110998])) (TableTree.leaf (#[6016790,6016790,6016790]))) (TableTree.node 187 (TableTree.leaf (#[6110990,6110990,6110990])) (TableTree.leaf (#[6016796,6016796,6016796])))))) (TableTree.node 195 (TableTree.node 191 (TableTree.node 189 (TableTree.leaf (#[6110990,6110990,6110990])) (TableTree.node 190 (TableTree.leaf (#[5777990,5777990,5777990])) (TableTree.leaf (#[5777990,5777990,5777990])))) (TableTree.node 193 (TableTree.node 192 (TableTree.leaf (#[5777990,5777990,5777990])) (TableTree.leaf (#[5777990,5777990,5777990]))) (TableTree.node 194 (TableTree.leaf (#[5777996,5777996,5777996])) (TableTree.leaf (#[5777999,5777999,5777999]))))) (TableTree.node 199 (TableTree.node 197 (TableTree.node 196 (TableTree.leaf (#[5778001,5778001,5778001])) (TableTree.leaf (#[5778000,5778000,5778000]))) (TableTree.node 198 (TableTree.leaf (#[5777990,5777990,5777990])) (TableTree.leaf (#[5888990,5888990,5888990])))) (TableTree.node 201 (TableTree.node 200 (TableTree.leaf (#[5888990,5888990,5888990])) (TableTree.leaf (#[5888990,5888990,5888990]))) (TableTree.node 202 (TableTree.leaf (#[5683793,5683793,5683793])) (TableTree.leaf (#[5888996,5888996,5888996]))))))) (TableTree.node 217 (TableTree.node 210 (TableTree.node 206 (TableTree.node 204 (TableTree.leaf (#[5888996,5888996,5888996])) (TableTree.node 205 (TableTree.leaf (#[5888999,5888999,5888999])) (TableTree.leaf (#[5888990,5888990,5888990])))) (TableTree.node 208 (TableTree.node 207 (TableTree.leaf (#[5999990,5999990,5999990])) (TableTree.leaf (#[5999990,5999990,5999990]))) (TableTree.node 209 (TableTree.leaf (#[5905787,5905787,5905787])) (TableTree.leaf (#[5999990,5999990,5999990]))))) (TableTree.node 213 (TableTree.node 211 (TableTree.leaf (#[5905790,5905790,5905790])) (TableTree.node 212 (TableTree.leaf (#[5999990,5999990,5999990])) (TableTree.leaf (#[5889001,5889001,5889001])))) (TableTree.node 215 (TableTree.node 214 (TableTree.leaf (#[6000000,6000000,6000000])) (TableTree.leaf (#[6000000,6000000,6000000]))) (TableTree.node 216 (TableTree.leaf (#[6000000,6000000,6000000])) (TableTree.leaf (#[5905787,5905787,5905787])))))) (TableTree.node 224 (TableTree.node 220 (TableTree.node 218 (TableTree.leaf (#[5999990,5999990,5999990])) (TableTree.node 219 (TableTree.leaf (#[5905793,5905793,5905793])) (TableTree.leaf (#[5999990,5999990,5999990])))) (TableTree.node 222 (TableTree.node 221 (TableTree.leaf (#[6016789,6016789,6016789])) (TableTree.leaf (#[6110990,6110990,6110990]))) (TableTree.node 223 (TableTree.leaf (#[6110993,6110993,6110993])) (TableTree.leaf (#[6110990,6110990,6110990]))))) (TableTree.node 228 (TableTree.node 226 (TableTree.node 225 (TableTree.leaf (#[5905792,5905792,5905792])) (TableTree.leaf (#[5905793,5905793,5905793]))) (TableTree.node 227 (TableTree.leaf (#[6016793,6016793,6016793])) (TableTree.leaf (#[6110996,6110996,6110996])))) (TableTree.node 230 (TableTree.node 229 (TableTree.leaf (#[6016790,6016790,6016790])) (TableTree.leaf (#[6110990,6110990,6110990]))) (TableTree.node 231 (TableTree.leaf (#[6016796,6016796,6016796])) (TableTree.leaf (#[6110990,6110990,6110990])))))))))) (TableTree.node 348 (TableTree.node 290 (TableTree.node 261 (TableTree.node 246 (TableTree.node 239 (TableTree.node 235 (TableTree.node 233 (TableTree.leaf (#[5888990,5888990,5888990])) (TableTree.node 234 (TableTree.leaf (#[5888995,5888995,5888995])) (TableTree.leaf (#[5888995,5888995,5888995])))) (TableTree.node 237 (TableTree.node 236 (TableTree.leaf (#[5888998,5888998,5888998])) (TableTree.leaf (#[5888990,5888990,5888990]))) (TableTree.node 238 (TableTree.leaf (#[5888990,5888990,5888990])) (TableTree.leaf (#[6110999,6110999,6110999]))))) (TableTree.node 242 (TableTree.node 240 (TableTree.leaf (#[6110998,6110998,6110998])) (TableTree.node 241 (TableTree.leaf (#[5888996,5888996,5888996])) (TableTree.leaf (#[5889000,5889000,5889000])))) (TableTree.node 244 (TableTree.node 243 (TableTree.leaf (#[5905790,5905790,5905790])) (TableTree.leaf (#[5905792,5905792,5905792]))) (TableTree.node 245 (TableTree.leaf (#[5999993,5999993,5999993])) (TableTree.leaf (#[5999996,5999996,5999996])))))) (TableTree.node 253 (TableTree.node 249 (TableTree.node 247 (TableTree.leaf (#[5999990,5999990,5999990])) (TableTree.node 248 (TableTree.leaf (#[5999990,5999990,5999990])) (TableTree.leaf (#[5905793,5905793,5905793])))) (TableTree.node 251 (TableTree.node 250 (TableTree.leaf (#[5905793,5905793,5905793])) (TableTree.leaf (#[5999996,5999996,5999996]))) (TableTree.node 252 (TableTree.leaf (#[5999996,5999996,5999996])) (TableTree.leaf (#[5999990,5999990,5999990]))))) (TableTree.node 257 (TableTree.node 255 (TableTree.node 254 (TableTree.leaf (#[5999990,5999990,5999990])) (TableTree.leaf (#[5905793,5905793,5905793]))) (TableTree.node 256 (TableTree.leaf (#[5999996,5999996,5999996])) (TableTree.leaf (#[5999999,5999999,5999999])))) (TableTree.node 259 (TableTree.node 258 (TableTree.leaf (#[5999998,5999998,5999998])) (TableTree.leaf (#[6016790,6016790,6016790]))) (TableTree.node 260 (TableTree.leaf (#[6016793,6016793,6016793])) (TableTree.leaf (#[6016790,6016790,6016790]))))))) (TableTree.node 275 (TableTree.node 268 (TableTree.node 264 (TableTree.node 262 (TableTree.leaf (#[6110993,6110993,6110993])) (TableTree.node 263 (TableTree.leaf (#[6110990,6110990,6110990])) (TableTree.leaf (#[6110990,6110990,6110990])))) (TableTree.node 266 (TableTree.node 265 (TableTree.leaf (#[6016796,6016796,6016796])) (TableTree.leaf (#[6016794,6016794,6016794]))) (TableTree.node 267 (TableTree.leaf (#[5888995,5888995,5888995])) (TableTree.leaf (#[6110990,6110990,6110990]))))) (TableTree.node 271 (TableTree.node 269 (TableTree.leaf (#[5888990,5888990,5888990])) (TableTree.node 270 (TableTree.leaf (#[5888990,5888990,5888990])) (TableTree.leaf (#[6110996,6110996,6110996])))) (TableTree.node 273 (TableTree.node 272 (TableTree.leaf (#[6110999,6110999,6110999])) (TableTree.leaf (#[6111001,6111001,6111001]))) (TableTree.node 274 (TableTree.leaf (#[5889000,5889000,5889000])) (TableTree.leaf (#[5794792,5794792,5794792])))))) (TableTree.node 282 (TableTree.node 278 (TableTree.node 276 (TableTree.leaf (#[5888995,5888995,5888995])) (TableTree.node 277 (TableTree.leaf (#[5794787,5794787,5794787])) (TableTree.leaf (#[5888990,5888990,5888990])))) (TableTree.node 280 (TableTree.node 279 (TableTree.leaf (#[5794790,5794790,5794790])) (TableTree.leaf (#[5888990,5888990,5888990]))) (TableTree.node 281 (TableTree.leaf (#[5999996,5999996,5999996])) (TableTree.leaf (#[5999999,5999999,5999999]))))) (TableTree.node 286 (TableTree.node 284 (TableTree.node 283 (TableTree.leaf (#[5905787,5905787,5905787])) (TableTree.leaf (#[5999990,5999990,5999990]))) (TableTree.node 285 (TableTree.leaf (#[5905793,5905793,5905793])) (TableTree.leaf (#[5999990,5999990,5999990])))) (TableTree.node 288 (TableTree.node 287 (TableTree.leaf (#[5794793,5794793,5794793])) (TableTree.leaf (#[5888996,5888996,5888996]))) (TableTree.node 289 (TableTree.leaf (#[5999996,5999996,5999996])) (TableTree.leaf (#[5999999,5999999,5999999])))))))) (TableTree.node 319 (TableTree.node 304 (TableTree.node 297 (TableTree.node 293 (TableTree.node 291 (TableTree.leaf (#[5905793,5905793,5905793])) (TableTree.node 292 (TableTree.leaf (#[5999997,5999997,5999997])) (TableTree.leaf (#[5905789,5905789,5905789])))) (TableTree.node 295 (TableTree.node 294 (TableTree.leaf (#[5999990,5999990,5999990])) (TableTree.leaf (#[5999993,5999993,5999993]))) (TableTree.node 296 (TableTree.leaf (#[5999990,5999990,5999990])) (TableTree.leaf (#[5905794,5905794,5905794]))))) (TableTree.node 300 (TableTree.node 298 (TableTree.leaf (#[5999997,5999997,5999997])) (TableTree.node 299 (TableTree.leaf (#[5905790,5905790,5905790])) (TableTree.leaf (#[5999990,5999990,5999990])))) (TableTree.node 302 (TableTree.node 301 (TableTree.leaf (#[5905796,5905796,5905796])) (TableTree.leaf (#[5999990,5999990,5999990]))) (TableTree.node 303 (TableTree.leaf (#[6000001,6000001,6000001])) (TableTree.leaf (#[6000000,6000000,6000000])))))) (TableTree.node 311 (TableTree.node 307 (TableTree.node 305 (TableTree.leaf (#[6000000,6000000,6000000])) (TableTree.node 306 (TableTree.leaf (#[6000000,6000000,6000000])) (TableTree.leaf (#[5888990,5888990,5888990])))) (TableTree.node 309 (TableTree.node 308 (TableTree.leaf (#[5888990,5888990,5888990])) (TableTree.leaf (#[5794787,5794787,5794787]))) (TableTree.node 310 (TableTree.leaf (#[5888990,5888990,5888990])) (TableTree.leaf (#[5794790,5794790,5794790]))))) (TableTree.node 315 (TableTree.node 313 (TableTree.node 312 (TableTree.leaf (#[5888990,5888990,5888990])) (TableTree.leaf (#[5905787,5905787,5905787]))) (TableTree.node 314 (TableTree.leaf (#[5999990,5999990,5999990])) (TableTree.leaf (#[5905793,5905793,5905793])))) (TableTree.node 317 (TableTree.node 316 (TableTree.leaf (#[5999990,5999990,5999990])) (TableTree.leaf (#[5905789,5905789,5905789]))) (TableTree.node 318 (TableTree.leaf (#[5999990,5999990,5999990])) (TableTree.leaf (#[5999993,5999993,5999993]))))))) (TableTree.node 333 (TableTree.node 326 (TableTree.node 322 (TableTree.node 320 (TableTree.leaf (#[5999990,5999990,5999990])) (TableTree.node 321 (TableTree.leaf (#[5905790,5905790,5905790])) (TableTree.leaf (#[5999990,5999990,5999990])))) (TableTree.node 324 (TableTree.node 323 (TableTree.leaf (#[5905796,5905796,5905796])) (TableTree.leaf (#[5999990,5999990,5999990]))) (TableTree.node 325 (TableTree.leaf (#[5999990,5999990,5999990])) (TableTree.leaf (#[5999995,5999995,5999995]))))) (TableTree.node 329 (TableTree.node 327 (TableTree.leaf (#[5999995,5999995,5999995])) (TableTree.node 328 (TableTree.leaf (#[5999998,5999998,5999998])) (TableTree.leaf (#[5999990,5999990,5999990])))) (TableTree.node 331 (TableTree.node 330 (TableTree.leaf (#[5999990,5999990,5999990])) (TableTree.leaf (#[5905790,5905790,5905790]))) (TableTree.node 332 (TableTree.leaf (#[5905792,5905792,5905792])) (TableTree.leaf (#[5999993,5999993,5999993])))))) (TableTree.node 340 (TableTree.node 336 (TableTree.node 334 (TableTree.leaf (#[5999996,5999996,5999996])) (TableTree.node 335 (TableTree.leaf (#[5999990,5999990,5999990])) (TableTree.leaf (#[5999990,5999990,5999990])))) (TableTree.node 338 (TableTree.node 337 (TableTree.leaf (#[5905793,5905793,5905793])) (TableTree.leaf (#[5905793,5905793,5905793]))) (TableTree.node 339 (TableTree.leaf (#[5999996,5999996,5999996])) (TableTree.leaf (#[5999996,5999996,5999996]))))) (TableTree.node 344 (TableTree.node 342 (TableTree.node 341 (TableTree.leaf (#[5999990,5999990,5999990])) (TableTree.leaf (#[5999990,5999990,5999990]))) (TableTree.node 343 (TableTree.leaf (#[5905790,5905790,5905790])) (TableTree.leaf (#[5905793,5905793,5905793])))) (TableTree.node 346 (TableTree.node 345 (TableTree.leaf (#[5905790,5905790,5905790])) (TableTree.leaf (#[5999993,5999993,5999993]))) (TableTree.node 347 (TableTree.leaf (#[5999990,5999990,5999990])) (TableTree.leaf (#[5999990,5999990,5999990]))))))))) (TableTree.node 406 (TableTree.node 377 (TableTree.node 362 (TableTree.node 355 (TableTree.node 351 (TableTree.node 349 (TableTree.leaf (#[6016796,6016796,6016796])) (TableTree.node 350 (TableTree.leaf (#[6016794,6016794,6016794])) (TableTree.leaf (#[5999995,5999995,5999995])))) (TableTree.node 353 (TableTree.node 352 (TableTree.leaf (#[6110990,6110990,6110990])) (TableTree.leaf (#[5905792,5905792,5905792]))) (TableTree.node 354 (TableTree.leaf (#[5999995,5999995,5999995])) (TableTree.leaf (#[5999996,5999996,5999996]))))) (TableTree.node 358 (TableTree.node 356 (TableTree.leaf (#[5999999,5999999,5999999])) (TableTree.node 357 (TableTree.leaf (#[6016793,6016793,6016793])) (TableTree.leaf (#[6110997,6110997,6110997])))) (TableTree.node 360 (TableTree.node 359 (TableTree.leaf (#[6016794,6016794,6016794])) (TableTree.leaf (#[6110997,6110997,6110997]))) (TableTree.node 361 (TableTree.leaf (#[5888996,5888996,5888996])) (TableTree.leaf (#[5888999,5888999,5888999])))))) (TableTree.node 369 (TableTree.node 365 (TableTree.node 363 (TableTree.leaf (#[5889001,5889001,5889001])) (TableTree.node 364 (TableTree.leaf (#[6000000,6000000,6000000])) (TableTree.leaf (#[5905793,5905793,5905793])))) (TableTree.node 367 (TableTree.node 366 (TableTree.leaf (#[5999996,5999996,5999996])) (TableTree.leaf (#[5999996,5999996,5999996]))) (TableTree.node 368 (TableTree.leaf (#[5999999,5999999,5999999])) (TableTree.leaf (#[6000001,6000001,6000001]))))) (TableTree.node 373 (TableTree.node 371 (TableTree.node 370 (TableTree.leaf (#[5889000,5889000,5889000])) (TableTree.leaf (#[5889000,5889000,5889000]))) (TableTree.node 372 (TableTree.leaf (#[5889000,5889000,5889000])) (TableTree.leaf (#[5905792,5905792,5905792])))) (TableTree.node 375 (TableTree.node 374 (TableTree.leaf (#[5905793,5905793,5905793])) (TableTree.leaf (#[5999998,5999998,5999998]))) (TableTree.node 376 (TableTree.leaf (#[5999996,5999996,5999996])) (TableTree.leaf (#[6000000,6000000,6000000]))))))) (TableTree.node 391 (TableTree.node 384 (TableTree.node 380 (TableTree.node 378 (TableTree.leaf (#[5999990,5999990,5999990])) (TableTree.node 379 (TableTree.leaf (#[5999995,5999995,5999995])) (TableTree.leaf (#[5999995,5999995,5999995])))) (TableTree.node 382 (TableTree.node 381 (TableTree.leaf (#[5999998,5999998,5999998])) (TableTree.leaf (#[5999990,5999990,5999990]))) (TableTree.node 383 (TableTree.leaf (#[5999990,5999990,5999990])) (TableTree.leaf (#[5905793,5905793,5905793]))))) (TableTree.node 387 (TableTree.node 385 (TableTree.leaf (#[5999996,5999996,5999996])) (TableTree.node 386 (TableTree.leaf (#[5999999,5999999,5999999])) (TableTree.leaf (#[5999998,5999998,5999998])))) (TableTree.node 389 (TableTree.node 388 (TableTree.leaf (#[5905790,5905790,5905790])) (TableTree.leaf (#[5905792,5905792,5905792]))) (TableTree.node 390 (TableTree.leaf (#[5999993,5999993,5999993])) (TableTree.leaf (#[5999996,5999996,5999996])))))) (TableTree.node 398 (TableTree.node 394 (TableTree.node 392 (TableTree.leaf (#[5999990,5999990,5999990])) (TableTree.node 393 (TableTree.leaf (#[5999990,5999990,5999990])) (TableTree.leaf (#[5905793,5905793,5905793])))) (TableTree.node 396 (TableTree.node 395 (TableTree.leaf (#[5905793,5905793,5905793])) (TableTree.leaf (#[5999996,5999996,5999996]))) (TableTree.node 397 (TableTree.leaf (#[5999996,5999996,5999996])) (TableTree.leaf (#[5999990,5999990,5999990]))))) (TableTree.node 402 (TableTree.node 400 (TableTree.node 399 (TableTree.leaf (#[5999990,5999990,5999990])) (TableTree.leaf (#[5999996,5999996,5999996]))) (TableTree.node 401 (TableTree.leaf (#[5999999,5999999,5999999])) (TableTree.leaf (#[6000001,6000001,6000001])))) (TableTree.node 404 (TableTree.node 403 (TableTree.leaf (#[6000000,6000000,6000000])) (TableTree.leaf (#[5905790,5905790,5905790]))) (TableTree.node 405 (TableTree.leaf (#[5905793,5905793,5905793])) (TableTree.leaf (#[5905790,5905790,5905790])))))))) (TableTree.node 435 (TableTree.node 420 (TableTree.node 413 (TableTree.node 409 (TableTree.node 407 (TableTree.leaf (#[5999993,5999993,5999993])) (TableTree.node 408 (TableTree.leaf (#[5999990,5999990,5999990])) (TableTree.leaf (#[5999990,5999990,5999990])))) (TableTree.node 411 (TableTree.node 410 (TableTree.leaf (#[5905796,5905796,5905796])) (TableTree.leaf (#[5905794,5905794,5905794]))) (TableTree.node 412 (TableTree.leaf (#[5999990,5999990,5999990])) (TableTree.leaf (#[5905793,5905793,5905793]))))) (TableTree.node 416 (TableTree.node 414 (TableTree.leaf (#[5999996,5999996,5999996])) (TableTree.node 415 (TableTree.leaf (#[5905792,5905792,5905792])) (TableTree.leaf (#[5999995,5999995,5999995])))) (TableTree.node 418 (TableTree.node 417 (TableTree.leaf (#[5905787,5905787,5905787])) (TableTree.leaf (#[5999999,5999999,5999999]))) (TableTree.node 419 (TableTree.leaf (#[5905787,5905787,5905787])) (TableTree.leaf (#[6000001,6000001,6000001])))))) (TableTree.node 427 (TableTree.node 423 (TableTree.node 421 (TableTree.leaf (#[6000000,6000000,6000000])) (TableTree.node 422 (TableTree.leaf (#[6000000,6000000,6000000])) (TableTree.leaf (#[6000000,6000000,6000000])))) (TableTree.node 425 (TableTree.node 424 (TableTree.leaf (#[5905793,5905793,5905793])) (TableTree.leaf (#[5999997,5999997,5999997]))) (TableTree.node 426 (TableTree.leaf (#[5905789,5905789,5905789])) (TableTree.leaf (#[5999993,5999993,5999993]))))) (TableTree.node 431 (TableTree.node 429 (TableTree.node 428 (TableTree.leaf (#[5905794,5905794,5905794])) (TableTree.leaf (#[5999997,5999997,5999997]))) (TableTree.node 430 (TableTree.leaf (#[5999996,5999996,5999996])) (TableTree.leaf (#[5999999,5999999,5999999])))) (TableTree.node 433 (TableTree.node 432 (TableTree.leaf (#[6000001,6000001,6000001])) (TableTree.leaf (#[6000000,6000000,6000000]))) (TableTree.node 434 (TableTree.leaf (#[6000000,6000000,6000000])) (TableTree.leaf (#[6000000,6000000,6000000]))))))) (TableTree.node 449 (TableTree.node 442 (TableTree.node 438 (TableTree.node 436 (TableTree.leaf (#[6000000,6000000,6000000])) (TableTree.node 437 (TableTree.leaf (#[5905793,5905793,5905793])) (TableTree.leaf (#[5999998,5999998,5999998])))) (TableTree.node 440 (TableTree.node 439 (TableTree.leaf (#[6000000,6000000,6000000])) (TableTree.leaf (#[4889995,4889995,4889995]))) (TableTree.node 441 (TableTree.leaf (#[4889990,4889990,4889990])) (TableTree.leaf (#[4889990,4889990,4889990]))))) (TableTree.node 445 (TableTree.node 443 (TableTree.leaf (#[4906792,4906792,4906792])) (TableTree.node 444 (TableTree.leaf (#[5000995,5000995,5000995])) (TableTree.leaf (#[4906787,4906787,4906787])))) (TableTree.node 447 (TableTree.node 446 (TableTree.leaf (#[5000990,5000990,5000990])) (TableTree.leaf (#[4906790,4906790,4906790]))) (TableTree.node 448 (TableTree.leaf (#[5000990,5000990,5000990])) (TableTree.leaf (#[5000996,5000996,5000996])))))) (TableTree.node 456 (TableTree.node 452 (TableTree.node 450 (TableTree.leaf (#[5000999,5000999,5000999])) (TableTree.node 451 (TableTree.leaf (#[4906787,4906787,4906787])) (TableTree.leaf (#[5000990,5000990,5000990])))) (TableTree.node 454 (TableTree.node 453 (TableTree.leaf (#[4906793,4906793,4906793])) (TableTree.leaf (#[5000990,5000990,5000990]))) (TableTree.node 455 (TableTree.leaf (#[5905792,5905792,5905792])) (TableTree.leaf (#[5905793,5905793,5905793]))))) (TableTree.node 460 (TableTree.node 458 (TableTree.node 457 (TableTree.leaf (#[4889996,4889996,4889996])) (TableTree.leaf (#[4906793,4906793,4906793]))) (TableTree.node 459 (TableTree.leaf (#[5000996,5000996,5000996])) (TableTree.leaf (#[5000996,5000996,5000996])))) (TableTree.node 462 (TableTree.node 461 (TableTree.leaf (#[5000999,5000999,5000999])) (TableTree.leaf (#[4906793,4906793,4906793]))) (TableTree.node 463 (TableTree.leaf (#[5000997,5000997,5000997])) (TableTree.leaf (#[4906789,4906789,4906789]))))))))))) (TableTree.node 696 (TableTree.node 580 (TableTree.node 522 (TableTree.node 493 (TableTree.node 478 (TableTree.node 471 (TableTree.node 467 (TableTree.node 465 (TableTree.leaf (#[5000990,5000990,5000990])) (TableTree.node 466 (TableTree.leaf (#[5000993,5000993,5000993])) (TableTree.leaf (#[5000990,5000990,5000990])))) (TableTree.node 469 (TableTree.node 468 (TableTree.leaf (#[4906794,4906794,4906794])) (TableTree.leaf (#[5000997,5000997,5000997]))) (TableTree.node 470 (TableTree.leaf (#[4906790,4906790,4906790])) (TableTree.leaf (#[5000990,5000990,5000990]))))) (TableTree.node 474 (TableTree.node 472 (TableTree.leaf (#[4906796,4906796,4906796])) (TableTree.node 473 (TableTree.leaf (#[5000990,5000990,5000990])) (TableTree.leaf (#[5000990,5000990,5000990])))) (TableTree.node 476 (TableTree.node 475 (TableTree.leaf (#[5000995,5000995,5000995])) (TableTree.leaf (#[5000995,5000995,5000995]))) (TableTree.node 477 (TableTree.leaf (#[5000998,5000998,5000998])) (TableTree.leaf (#[5000993,5000993,5000993])))))) (TableTree.node 485 (TableTree.node 481 (TableTree.node 479 (TableTree.leaf (#[5000996,5000996,5000996])) (TableTree.node 480 (TableTree.leaf (#[5001000,5001000,5001000])) (TableTree.leaf (#[5001000,5001000,5001000])))) (TableTree.node 483 (TableTree.node 482 (TableTree.leaf (#[5000999,5000999,5000999])) (TableTree.leaf (#[5001000,5001000,5001000]))) (TableTree.node 484 (TableTree.leaf (#[5000998,5000998,5000998])) (TableTree.leaf (#[5000997,5000997,5000997]))))) (TableTree.node 489 (TableTree.node 487 (TableTree.node 486 (TableTree.leaf (#[5000990,5000990,5000990])) (TableTree.leaf (#[5000990,5000990,5000990]))) (TableTree.node 488 (TableTree.leaf (#[5000990,5000990,5000990])) (TableTree.leaf (#[5000990,5000990,5000990])))) (TableTree.node 491 (TableTree.node 490 (TableTree.leaf (#[5001001,5001001,5001001])) (TableTree.leaf (#[5001000,5001000,5001000]))) (TableTree.node 492 (TableTree.leaf (#[5001000,5001000,5001000])) (TableTree.leaf (#[5001000,5001000,5001000]))))))) (TableTree.node 507 (TableTree.node 500 (TableTree.node 496 (TableTree.node 494 (TableTree.leaf (#[5001000,5001000,5001000])) (TableTree.node 495 (TableTree.leaf (#[5001000,5001000,5001000])) (TableTree.leaf (#[5001000,5001000,5001000])))) (TableTree.node 498 (TableTree.node 497 (TableTree.leaf (#[5001000,5001000,5001000])) (TableTree.leaf (#[5017793,5017793,5017793]))) (TableTree.node 499 (TableTree.leaf (#[5017793,5017793,5017793])) (TableTree.leaf (#[5111996,5111996,5111996]))))) (TableTree.node 503 (TableTree.node 501 (TableTree.leaf (#[5111996,5111996,5111996])) (TableTree.node 502 (TableTree.leaf (#[5017790,5017790,5017790])) (TableTree.leaf (#[5111993,5111993,5111993])))) (TableTree.node 505 (TableTree.node 504 (TableTree.leaf (#[5111993,5111993,5111993])) (TableTree.leaf (#[5111997,5111997,5111997]))) (TableTree.node 506 (TableTree.leaf (#[5111998,5111998,5111998])) (TableTree.leaf (#[5112000,5112000,5112000])))))) (TableTree.node 514 (TableTree.node 510 (TableTree.node 508 (TableTree.leaf (#[5111994,5111994,5111994])) (TableTree.node 509 (TableTree.leaf (#[5111997,5111997,5111997])) (TableTree.leaf (#[5111990,5111990,5111990])))) (TableTree.node 512 (TableTree.node 511 (TableTree.leaf (#[5111990,5111990,5111990])) (TableTree.leaf (#[5111990,5111990,5111990]))) (TableTree.node 513 (TableTree.leaf (#[5111990,5111990,5111990])) (TableTree.leaf (#[5017796,5017796,5017796]))))) (TableTree.node 518 (TableTree.node 516 (TableTree.node 515 (TableTree.leaf (#[5017794,5017794,5017794])) (TableTree.leaf (#[5888995,5888995,5888995]))) (TableTree.node 517 (TableTree.leaf (#[5017791,5017791,5017791])) (TableTree.leaf (#[5888991,5888991,5888991])))) (TableTree.node 520 (TableTree.node 519 (TableTree.leaf (#[5888997,5888997,5888997])) (TableTree.leaf (#[5888992,5888992,5888992]))) (TableTree.node 521 (TableTree.leaf (#[5888998,5888998,5888998])) (TableTree.leaf (#[5111990,5111990,5111990])))))))) (TableTree.node 551 (TableTree.node 536 (TableTree.node 529 (TableTree.node 525 (TableTree.node 523 (TableTree.leaf (#[5017793,5017793,5017793])) (TableTree.node 524 (TableTree.leaf (#[5111996,5111996,5111996])) (TableTree.leaf (#[5111996,5111996,5111996])))) (TableTree.node 527 (TableTree.node 526 (TableTree.leaf (#[5111999,5111999,5111999])) (TableTree.leaf (#[5112001,5112001,5112001]))) (TableTree.node 528 (TableTree.leaf (#[5905792,5905792,5905792])) (TableTree.leaf (#[5999992,5999992,5999992]))))) (TableTree.node 532 (TableTree.node 530 (TableTree.leaf (#[5905793,5905793,5905793])) (TableTree.node 531 (TableTree.leaf (#[5999997,5999997,5999997])) (TableTree.leaf (#[5999994,5999994,5999994])))) (TableTree.node 534 (TableTree.node 533 (TableTree.leaf (#[5905794,5905794,5905794])) (TableTree.leaf (#[5999997,5999997,5999997]))) (TableTree.node 535 (TableTree.leaf (#[5905793,5905793,5905793])) (TableTree.leaf (#[5999996,5999996,5999996])))))) (TableTree.node 543 (TableTree.node 539 (TableTree.node 537 (TableTree.leaf (#[5222993,5222993,5222993])) (TableTree.node 538 (TableTree.leaf (#[5222996,5222996,5222996])) (TableTree.leaf (#[5222990,5222990,5222990])))) (TableTree.node 541 (TableTree.node 540 (TableTree.leaf (#[5222995,5222995,5222995])) (TableTree.leaf (#[5222995,5222995,5222995]))) (TableTree.node 542 (TableTree.leaf (#[5222998,5222998,5222998])) (TableTree.leaf (#[5222990,5222990,5222990]))))) (TableTree.node 547 (TableTree.node 545 (TableTree.node 544 (TableTree.leaf (#[5222990,5222990,5222990])) (TableTree.leaf (#[5999996,5999996,5999996]))) (TableTree.node 546 (TableTree.leaf (#[5999999,5999999,5999999])) (TableTree.leaf (#[6000001,6000001,6000001])))) (TableTree.node 549 (TableTree.node 548 (TableTree.leaf (#[6000000,6000000,6000000])) (TableTree.leaf (#[6000000,6000000,6000000]))) (TableTree.node 550 (TableTree.leaf (#[6000000,6000000,6000000])) (TableTree.leaf (#[5223000,5223000,5223000]))))))) (TableTree.node 565 (TableTree.node 558 (TableTree.node 554 (TableTree.node 552 (TableTree.leaf (#[5223000,5223000,5223000])) (TableTree.node 553 (TableTree.leaf (#[5128790,5128790,5128790])) (TableTree.leaf (#[5222993,5222993,5222993])))) (TableTree.node 556 (TableTree.node 555 (TableTree.leaf (#[5222996,5222996,5222996])) (TableTree.leaf (#[5222995,5222995,5222995]))) (TableTree.node 557 (TableTree.leaf (#[5128790,5128790,5128790])) (TableTree.leaf (#[5128792,5128792,5128792]))))) (TableTree.node 561 (TableTree.node 559 (TableTree.leaf (#[5222993,5222993,5222993])) (TableTree.node 560 (TableTree.leaf (#[5222996,5222996,5222996])) (TableTree.leaf (#[5222990,5222990,5222990])))) (TableTree.node 563 (TableTree.node 562 (TableTree.leaf (#[5222990,5222990,5222990])) (TableTree.leaf (#[5128793,5128793,5128793]))) (TableTree.node 564 (TableTree.leaf (#[5128793,5128793,5128793])) (TableTree.leaf (#[5222996,5222996,5222996])))))) (TableTree.node 572 (TableTree.node 568 (TableTree.node 566 (TableTree.leaf (#[5222996,5222996,5222996])) (TableTree.node 567 (TableTree.leaf (#[5222990,5222990,5222990])) (TableTree.leaf (#[5222990,5222990,5222990])))) (TableTree.node 570 (TableTree.node 569 (TableTree.leaf (#[5333994,5333994,5333994])) (TableTree.leaf (#[5333997,5333997,5333997]))) (TableTree.node 571 (TableTree.leaf (#[5333999,5333999,5333999])) (TableTree.leaf (#[5334000,5334000,5334000]))))) (TableTree.node 576 (TableTree.node 574 (TableTree.node 573 (TableTree.leaf (#[5239790,5239790,5239790])) (TableTree.leaf (#[5239793,5239793,5239793]))) (TableTree.node 575 (TableTree.leaf (#[5239790,5239790,5239790])) (TableTree.leaf (#[5333993,5333993,5333993])))) (TableTree.node 578 (TableTree.node 577 (TableTree.leaf (#[5333990,5333990,5333990])) (TableTree.leaf (#[5333990,5333990,5333990]))) (TableTree.node 579 (TableTree.leaf (#[5239796,5239796,5239796])) (TableTree.leaf (#[5239794,5239794,5239794]))))))))) (TableTree.node 638 (TableTree.node 609 (TableTree.node 594 (TableTree.node 587 (TableTree.node 583 (TableTree.node 581 (TableTree.leaf (#[5333995,5333995,5333995])) (TableTree.node 582 (TableTree.leaf (#[5333990,5333990,5333990])) (TableTree.leaf (#[5333990,5333990,5333990])))) (TableTree.node 585 (TableTree.node 584 (TableTree.leaf (#[5333990,5333990,5333990])) (TableTree.leaf (#[5128793,5128793,5128793]))) (TableTree.node 586 (TableTree.leaf (#[5222996,5222996,5222996])) (TableTree.leaf (#[5222999,5222999,5222999]))))) (TableTree.node 590 (TableTree.node 588 (TableTree.leaf (#[5222998,5222998,5222998])) (TableTree.node 589 (TableTree.leaf (#[5333996,5333996,5333996])) (TableTree.leaf (#[5333999,5333999,5333999])))) (TableTree.node 592 (TableTree.node 591 (TableTree.leaf (#[5334001,5334001,5334001])) (TableTree.leaf (#[5239793,5239793,5239793]))) (TableTree.node 593 (TableTree.leaf (#[5333996,5333996,5333996])) (TableTree.leaf (#[5333996,5333996,5333996])))))) (TableTree.node 601 (TableTree.node 597 (TableTree.node 595 (TableTree.leaf (#[5333999,5333999,5333999])) (TableTree.node 596 (TableTree.leaf (#[5239792,5239792,5239792])) (TableTree.leaf (#[5333995,5333995,5333995])))) (TableTree.node 599 (TableTree.node 598 (TableTree.leaf (#[5239787,5239787,5239787])) (TableTree.leaf (#[5333990,5333990,5333990]))) (TableTree.node 600 (TableTree.leaf (#[5239790,5239790,5239790])) (TableTree.leaf (#[5333990,5333990,5333990]))))) (TableTree.node 605 (TableTree.node 603 (TableTree.node 602 (TableTree.leaf (#[5333996,5333996,5333996])) (TableTree.leaf (#[5333999,5333999,5333999]))) (TableTree.node 604 (TableTree.leaf (#[5239787,5239787,5239787])) (TableTree.leaf (#[5333990,5333990,5333990])))) (TableTree.node 607 (TableTree.node 606 (TableTree.leaf (#[5239793,5239793,5239793])) (TableTree.leaf (#[5333990,5333990,5333990]))) (TableTree.node 608 (TableTree.leaf (#[5239793,5239793,5239793])) (TableTree.leaf (#[5333996,5333996,5333996]))))))) (TableTree.node 623 (TableTree.node 616 (TableTree.node 612 (TableTree.node 610 (TableTree.leaf (#[5333999,5333999,5333999])) (TableTree.node 611 (TableTree.leaf (#[5333998,5333998,5333998])) (TableTree.leaf (#[5239793,5239793,5239793])))) (TableTree.node 614 (TableTree.node 613 (TableTree.leaf (#[5333997,5333997,5333997])) (TableTree.leaf (#[5239789,5239789,5239789]))) (TableTree.node 615 (TableTree.leaf (#[5333990,5333990,5333990])) (TableTree.leaf (#[5333993,5333993,5333993]))))) (TableTree.node 619 (TableTree.node 617 (TableTree.leaf (#[5333990,5333990,5333990])) (TableTree.node 618 (TableTree.leaf (#[5239794,5239794,5239794])) (TableTree.leaf (#[5333997,5333997,5333997])))) (TableTree.node 621 (TableTree.node 620 (TableTree.leaf (#[5239790,5239790,5239790])) (TableTree.leaf (#[5333990,5333990,5333990]))) (TableTree.node 622 (TableTree.leaf (#[5239796,5239796,5239796])) (TableTree.leaf (#[5333990,5333990,5333990])))))) (TableTree.node 630 (TableTree.node 626 (TableTree.node 624 (TableTree.leaf (#[5334000,5334000,5334000])) (TableTree.node 625 (TableTree.leaf (#[5334000,5334000,5334000])) (TableTree.leaf (#[5334000,5334000,5334000])))) (TableTree.node 628 (TableTree.node 627 (TableTree.leaf (#[5334000,5334000,5334000])) (TableTree.leaf (#[5334000,5334000,5334000]))) (TableTree.node 629 (TableTree.leaf (#[5334000,5334000,5334000])) (TableTree.leaf (#[5334000,5334000,5334000]))))) (TableTree.node 634 (TableTree.node 632 (TableTree.node 631 (TableTree.leaf (#[5334000,5334000,5334000])) (TableTree.leaf (#[5999995,5999995,5999995]))) (TableTree.node 633 (TableTree.leaf (#[5999998,5999998,5999998])) (TableTree.leaf (#[5905792,5905792,5905792])))) (TableTree.node 636 (TableTree.node 635 (TableTree.leaf (#[5999993,5999993,5999993])) (TableTree.leaf (#[5905793,5905793,5905793]))) (TableTree.node 637 (TableTree.leaf (#[6110996,6110996,6110996])) (TableTree.leaf (#[6110996,6110996,6110996])))))))) (TableTree.node 667 (TableTree.node 652 (TableTree.node 645 (TableTree.node 641 (TableTree.node 639 (TableTree.leaf (#[6016790,6016790,6016790])) (TableTree.node 640 (TableTree.leaf (#[6016793,6016793,6016793])) (TableTree.leaf (#[6110993,6110993,6110993])))) (TableTree.node 643 (TableTree.node 642 (TableTree.leaf (#[6016794,6016794,6016794])) (TableTree.leaf (#[5777990,5777990,5777990]))) (TableTree.node 644 (TableTree.leaf (#[5777995,5777995,5777995])) (TableTree.leaf (#[5777995,5777995,5777995]))))) (TableTree.node 648 (TableTree.node 646 (TableTree.leaf (#[5777998,5777998,5777998])) (TableTree.node 647 (TableTree.leaf (#[5777993,5777993,5777993])) (TableTree.leaf (#[5777996,5777996,5777996])))) (TableTree.node 650 (TableTree.node 649 (TableTree.leaf (#[5778000,5778000,5778000])) (TableTree.leaf (#[5778000,5778000,5778000]))) (TableTree.node 651 (TableTree.leaf (#[5777999,5777999,5777999])) (TableTree.leaf (#[5778000,5778000,5778000])))))) (TableTree.node 659 (TableTree.node 655 (TableTree.node 653 (TableTree.leaf (#[5777998,5777998,5777998])) (TableTree.node 654 (TableTree.leaf (#[5777997,5777997,5777997])) (TableTree.leaf (#[5777990,5777990,5777990])))) (TableTree.node 657 (TableTree.node 656 (TableTree.leaf (#[5777990,5777990,5777990])) (TableTree.leaf (#[5777990,5777990,5777990]))) (TableTree.node 658 (TableTree.leaf (#[5777990,5777990,5777990])) (TableTree.leaf (#[5683793,5683793,5683793]))))) (TableTree.node 663 (TableTree.node 661 (TableTree.node 660 (TableTree.leaf (#[5683793,5683793,5683793])) (TableTree.leaf (#[5777996,5777996,5777996]))) (TableTree.node 662 (TableTree.leaf (#[5777996,5777996,5777996])) (TableTree.leaf (#[5683790,5683790,5683790])))) (TableTree.node 665 (TableTree.node 664 (TableTree.leaf (#[5777993,5777993,5777993])) (TableTree.leaf (#[5777993,5777993,5777993]))) (TableTree.node 666 (TableTree.leaf (#[5777997,5777997,5777997])) (TableTree.leaf (#[5777998,5777998,5777998]))))))) (TableTree.node 681 (TableTree.node 674 (TableTree.node 670 (TableTree.node 668 (TableTree.leaf (#[5778000,5778000,5778000])) (TableTree.node 669 (TableTree.leaf (#[5777994,5777994,5777994])) (TableTree.leaf (#[5777997,5777997,5777997])))) (TableTree.node 672 (TableTree.node 671 (TableTree.leaf (#[5777990,5777990,5777990])) (TableTree.leaf (#[5777990,5777990,5777990]))) (TableTree.node 673 (TableTree.leaf (#[5777990,5777990,5777990])) (TableTree.leaf (#[5777990,5777990,5777990]))))) (TableTree.node 677 (TableTree.node 675 (TableTree.leaf (#[5683796,5683796,5683796])) (TableTree.node 676 (TableTree.leaf (#[5683794,5683794,5683794])) (TableTree.leaf (#[5777995,5777995,5777995])))) (TableTree.node 679 (TableTree.node 678 (TableTree.leaf (#[5683791,5683791,5683791])) (TableTree.leaf (#[5777991,5777991,5777991]))) (TableTree.node 680 (TableTree.leaf (#[5777997,5777997,5777997])) (TableTree.leaf (#[5777992,5777992,5777992])))))) (TableTree.node 688 (TableTree.node 684 (TableTree.node 682 (TableTree.leaf (#[5777998,5777998,5777998])) (TableTree.node 683 (TableTree.leaf (#[5777990,5777990,5777990])) (TableTree.leaf (#[5777990,5777990,5777990])))) (TableTree.node 686 (TableTree.node 685 (TableTree.leaf (#[5683787,5683787,5683787])) (TableTree.leaf (#[5683790,5683790,5683790]))) (TableTree.node 687 (TableTree.leaf (#[5683792,5683792,5683792])) (TableTree.leaf (#[5777992,5777992,5777992]))))) (TableTree.node 692 (TableTree.node 690 (TableTree.node 689 (TableTree.leaf (#[5683792,5683792,5683792])) (TableTree.leaf (#[5794793,5794793,5794793]))) (TableTree.node 691 (TableTree.leaf (#[5888997,5888997,5888997])) (TableTree.leaf (#[5888994,5888994,5888994])))) (TableTree.node 694 (TableTree.node 693 (TableTree.leaf (#[5683787,5683787,5683787])) (TableTree.leaf (#[5683793,5683793,5683793]))) (TableTree.node 695 (TableTree.leaf (#[5794789,5794789,5794789])) (TableTree.leaf (#[5888993,5888993,5888993])))))))))) (TableTree.node 812 (TableTree.node 754 (TableTree.node 725 (TableTree.node 710 (TableTree.node 703 (TableTree.node 699 (TableTree.node 697 (TableTree.leaf (#[5794794,5794794,5794794])) (TableTree.node 698 (TableTree.leaf (#[5888997,5888997,5888997])) (TableTree.leaf (#[5794793,5794793,5794793])))) (TableTree.node 701 (TableTree.node 700 (TableTree.leaf (#[5888996,5888996,5888996])) (TableTree.leaf (#[5999993,5999993,5999993]))) (TableTree.node 702 (TableTree.leaf (#[5999996,5999996,5999996])) (TableTree.leaf (#[5794790,5794790,5794790]))))) (TableTree.node 706 (TableTree.node 704 (TableTree.leaf (#[5794796,5794796,5794796])) (TableTree.node 705 (TableTree.leaf (#[5905790,5905790,5905790])) (TableTree.leaf (#[5999993,5999993,5999993])))) (TableTree.node 708 (TableTree.node 707 (TableTree.leaf (#[5999996,5999996,5999996])) (TableTree.leaf (#[5999995,5999995,5999995]))) (TableTree.node 709 (TableTree.leaf (#[5999994,5999994,5999994])) (TableTree.leaf (#[5999997,5999997,5999997])))))) (TableTree.node 717 (TableTree.node 713 (TableTree.node 711 (TableTree.leaf (#[5999999,5999999,5999999])) (TableTree.node 712 (TableTree.leaf (#[5905793,5905793,5905793])) (TableTree.leaf (#[5999998,5999998,5999998])))) (TableTree.node 715 (TableTree.node 714 (TableTree.leaf (#[5999996,5999996,5999996])) (TableTree.leaf (#[5999999,5999999,5999999]))) (TableTree.node 716 (TableTree.leaf (#[6000001,6000001,6000001])) (TableTree.leaf (#[6000000,6000000,6000000]))))) (TableTree.node 721 (TableTree.node 719 (TableTree.node 718 (TableTree.leaf (#[6000000,6000000,6000000])) (TableTree.leaf (#[6111000,6111000,6111000]))) (TableTree.node 720 (TableTree.leaf (#[6111000,6111000,6111000])) (TableTree.leaf (#[6111000,6111000,6111000])))) (TableTree.node 723 (TableTree.node 722 (TableTree.leaf (#[6016793,6016793,6016793])) (TableTree.leaf (#[6000000,6000000,6000000]))) (TableTree.node 724 (TableTree.leaf (#[6000000,6000000,6000000])) (TableTree.leaf (#[6000000,6000000,6000000]))))))) (TableTree.node 739 (TableTree.node 732 (TableTree.node 728 (TableTree.node 726 (TableTree.leaf (#[6016792,6016792,6016792])) (TableTree.node 727 (TableTree.leaf (#[6016793,6016793,6016793])) (TableTree.leaf (#[6000000,6000000,6000000])))) (TableTree.node 730 (TableTree.node 729 (TableTree.leaf (#[6000000,6000000,6000000])) (TableTree.leaf (#[5999999,5999999,5999999]))) (TableTree.node 731 (TableTree.leaf (#[6000000,6000000,6000000])) (TableTree.leaf (#[5999998,5999998,5999998]))))) (TableTree.node 735 (TableTree.node 733 (TableTree.leaf (#[5999997,5999997,5999997])) (TableTree.node 734 (TableTree.leaf (#[5905793,5905793,5905793])) (TableTree.leaf (#[5999996,5999996,5999996])))) (TableTree.node 737 (TableTree.node 736 (TableTree.leaf (#[6000000,6000000,6000000])) (TableTree.leaf (#[5905790,5905790,5905790]))) (TableTree.node 738 (TableTree.leaf (#[5999993,5999993,5999993])) (TableTree.leaf (#[5999998,5999998,5999998])))))) (TableTree.node 746 (TableTree.node 742 (TableTree.node 740 (TableTree.leaf (#[6000000,6000000,6000000])) (TableTree.node 741 (TableTree.leaf (#[5905791,5905791,5905791])) (TableTree.leaf (#[5999991,5999991,5999991])))) (TableTree.node 744 (TableTree.node 743 (TableTree.leaf (#[5999997,5999997,5999997])) (TableTree.leaf (#[5999992,5999992,5999992]))) (TableTree.node 745 (TableTree.leaf (#[5905792,5905792,5905792])) (TableTree.leaf (#[5999992,5999992,5999992]))))) (TableTree.node 750 (TableTree.node 748 (TableTree.node 747 (TableTree.leaf (#[5905792,5905792,5905792])) (TableTree.leaf (#[5999994,5999994,5999994]))) (TableTree.node 749 (TableTree.leaf (#[5999996,5999996,5999996])) (TableTree.leaf (#[6000000,6000000,6000000])))) (TableTree.node 752 (TableTree.node 751 (TableTree.leaf (#[5999993,5999993,5999993])) (TableTree.leaf (#[5999996,5999996,5999996]))) (TableTree.node 753 (TableTree.leaf (#[6000000,6000000,6000000])) (TableTree.leaf (#[6000000,6000000,6000000])))))))) (TableTree.node 783 (TableTree.node 768 (TableTree.node 761 (TableTree.node 757 (TableTree.node 755 (TableTree.leaf (#[5999999,5999999,5999999])) (TableTree.node 756 (TableTree.leaf (#[6000000,6000000,6000000])) (TableTree.leaf (#[5999998,5999998,5999998])))) (TableTree.node 759 (TableTree.node 758 (TableTree.leaf (#[5999997,5999997,5999997])) (TableTree.leaf (#[6000000,6000000,6000000]))) (TableTree.node 760 (TableTree.leaf (#[6000000,6000000,6000000])) (TableTree.leaf (#[6111001,6111001,6111001]))))) (TableTree.node 764 (TableTree.node 762 (TableTree.leaf (#[6111000,6111000,6111000])) (TableTree.node 763 (TableTree.leaf (#[5999997,5999997,5999997])) (TableTree.leaf (#[6110997,6110997,6110997])))) (TableTree.node 766 (TableTree.node 765 (TableTree.leaf (#[6111002,6111002,6111002])) (TableTree.leaf (#[6111001,6111001,6111001]))) (TableTree.node 767 (TableTree.leaf (#[6111002,6111002,6111002])) (TableTree.leaf (#[6111001,6111001,6111001])))))) (TableTree.node 775 (TableTree.node 771 (TableTree.node 769 (TableTree.leaf (#[6110998,6110998,6110998])) (TableTree.node 770 (TableTree.leaf (#[6110998,6110998,6110998])) (TableTree.leaf (#[6016791,6016791,6016791])))) (TableTree.node 773 (TableTree.node 772 (TableTree.leaf (#[6000001,6000001,6000001])) (TableTree.leaf (#[6000001,6000001,6000001]))) (TableTree.node 774 (TableTree.leaf (#[5999993,5999993,5999993])) (TableTree.leaf (#[5999991,5999991,5999991]))))) (TableTree.node 779 (TableTree.node 777 (TableTree.node 776 (TableTree.leaf (#[5999997,5999997,5999997])) (TableTree.leaf (#[5999994,5999994,5999994]))) (TableTree.node 778 (TableTree.leaf (#[6000000,6000000,6000000])) (TableTree.leaf (#[6016790,6016790,6016790])))) (TableTree.node 781 (TableTree.node 780 (TableTree.leaf (#[6016791,6016791,6016791])) (TableTree.leaf (#[6110994,6110994,6110994]))) (TableTree.node 782 (TableTree.leaf (#[5999994,5999994,5999994])) (TableTree.leaf (#[5999996,5999996,5999996]))))))) (TableTree.node 797 (TableTree.node 790 (TableTree.node 786 (TableTree.node 784 (TableTree.leaf (#[6111001,6111001,6111001])) (TableTree.node 785 (TableTree.leaf (#[6000000,6000000,6000000])) (TableTree.leaf (#[6000000,6000000,6000000])))) (TableTree.node 788 (TableTree.node 787 (TableTree.leaf (#[6000001,6000001,6000001])) (TableTree.leaf (#[6000000,6000000,6000000]))) (TableTree.node 789 (TableTree.leaf (#[5999997,5999997,5999997])) (TableTree.leaf (#[5999997,5999997,5999997]))))) (TableTree.node 793 (TableTree.node 791 (TableTree.leaf (#[6000002,6000002,6000002])) (TableTree.node 792 (TableTree.leaf (#[6000002,6000002,6000002])) (TableTree.leaf (#[6000001,6000001,6000001])))) (TableTree.node 795 (TableTree.node 794 (TableTree.leaf (#[5999998,5999998,5999998])) (TableTree.leaf (#[5999998,5999998,5999998]))) (TableTree.node 796 (TableTree.leaf (#[5999993,5999993,5999993])) (TableTree.leaf (#[5999991,5999991,5999991])))))) (TableTree.node 804 (TableTree.node 800 (TableTree.node 798 (TableTree.leaf (#[5999997,5999997,5999997])) (TableTree.node 799 (TableTree.leaf (#[5999994,5999994,5999994])) (TableTree.leaf (#[5905790,5905790,5905790])))) (TableTree.node 802 (TableTree.node 801 (TableTree.leaf (#[5905791,5905791,5905791])) (TableTree.leaf (#[5999994,5999994,5999994]))) (TableTree.node 803 (TableTree.leaf (#[6000003,6000003,6000003])) (TableTree.leaf (#[6000001,6000001,6000001]))))) (TableTree.node 808 (TableTree.node 806 (TableTree.node 805 (TableTree.leaf (#[5999999,5999999,5999999])) (TableTree.leaf (#[5999998,5999998,5999998]))) (TableTree.node 807 (TableTree.leaf (#[5999999,5999999,5999999])) (TableTree.leaf (#[5999999,5999999,5999999])))) (TableTree.node 810 (TableTree.node 809 (TableTree.leaf (#[5999996,5999996,5999996])) (TableTree.leaf (#[5999997,5999997,5999997]))) (TableTree.node 811 (TableTree.leaf (#[5999997,5999997,5999997])) (TableTree.leaf (#[5999997,5999997,5999997]))))))))) (TableTree.node 870 (TableTree.node 841 (TableTree.node 826 (TableTree.node 819 (TableTree.node 815 (TableTree.node 813 (TableTree.leaf (#[10673396,10673396,10673396])) (TableTree.node 814 (TableTree.leaf (#[10673396,10673396,10673396])) (TableTree.leaf (#[10673396,10673396,10673396])))) (TableTree.node 817 (TableTree.node 816 (TableTree.leaf (#[10673396,10673396,10673396])) (TableTree.leaf (#[10673396,10673396,10673396]))) (TableTree.node 818 (TableTree.leaf (#[10673396,10673396,10673396])) (TableTree.leaf (#[10673396,10673396,10673396]))))) (TableTree.node 822 (TableTree.node 820 (TableTree.leaf (#[10673396,10673396,10673396])) (TableTree.node 821 (TableTree.leaf (#[10673396,10673396,10673396])) (TableTree.leaf (#[5999990,10673396,10673396])))) (TableTree.node 824 (TableTree.node 823 (TableTree.leaf (#[5999995,10673396,10673396])) (TableTree.leaf (#[5999990,10673396,10673396]))) (TableTree.node 825 (TableTree.leaf (#[5999990,10673396,10673396])) (TableTree.leaf (#[5905793,10673396,10673396])))))) (TableTree.node 833 (TableTree.node 829 (TableTree.node 827 (TableTree.leaf (#[5999996,10673396,10673396])) (TableTree.node 828 (TableTree.leaf (#[5905790,10673396,10673396])) (TableTree.leaf (#[5905792,10673396,10673396])))) (TableTree.node 831 (TableTree.node 830 (TableTree.leaf (#[5999993,10673396,10673396])) (TableTree.leaf (#[5999996,10673396,10673396]))) (TableTree.node 832 (TableTree.leaf (#[5999990,10673396,10673396])) (TableTree.leaf (#[5999990,10673396,10673396]))))) (TableTree.node 837 (TableTree.node 835 (TableTree.node 834 (TableTree.leaf (#[5905793,10673396,10673396])) (TableTree.leaf (#[5905793,10673396,10673396]))) (TableTree.node 836 (TableTree.leaf (#[5999996,10673396,10673396])) (TableTree.leaf (#[5999996,10673396,10673396])))) (TableTree.node 839 (TableTree.node 838 (TableTree.leaf (#[5999990,10673396,10673396])) (TableTree.leaf (#[5999990,10673396,10673396]))) (TableTree.node 840 (TableTree.leaf (#[5999996,10673396,10673396])) (TableTree.leaf (#[5905790,10673396,10673396]))))))) (TableTree.node 855 (TableTree.node 848 (TableTree.node 844 (TableTree.node 842 (TableTree.leaf (#[5905793,10673396,10673396])) (TableTree.node 843 (TableTree.leaf (#[5905790,10673396,10673396])) (TableTree.leaf (#[5999993,10673396,10673396])))) (TableTree.node 846 (TableTree.node 845 (TableTree.leaf (#[5999990,10673396,10673396])) (TableTree.leaf (#[5999990,10673396,10673396]))) (TableTree.node 847 (TableTree.leaf (#[5905796,10673396,10673396])) (TableTree.leaf (#[5905794,10673396,10673396]))))) (TableTree.node 851 (TableTree.node 849 (TableTree.leaf (#[5999990,10673396,10673396])) (TableTree.node 850 (TableTree.leaf (#[5905793,10673396,10673396])) (TableTree.leaf (#[5999996,10673396,10673396])))) (TableTree.node 853 (TableTree.node 852 (TableTree.leaf (#[5905792,10673396,10673396])) (TableTree.leaf (#[5999995,10673396,10673396]))) (TableTree.node 854 (TableTree.leaf (#[5905787,10673396,10673396])) (TableTree.leaf (#[5905787,10673396,10673396])))))) (TableTree.node 862 (TableTree.node 858 (TableTree.node 856 (TableTree.leaf (#[5905793,10673396,10673396])) (TableTree.node 857 (TableTree.leaf (#[5999997,10673396,10673396])) (TableTree.leaf (#[5905789,10673396,10673396])))) (TableTree.node 860 (TableTree.node 859 (TableTree.leaf (#[5999993,10673396,10673396])) (TableTree.leaf (#[5905794,10673396,10673396]))) (TableTree.node 861 (TableTree.leaf (#[5999997,10673396,10673396])) (TableTree.leaf (#[5999996,10673396,10673396]))))) (TableTree.node 866 (TableTree.node 864 (TableTree.node 863 (TableTree.leaf (#[5905793,10673396,10673396])) (TableTree.leaf (#[5905792,10673396,10673396]))) (TableTree.node 865 (TableTree.leaf (#[5905793,10673396,10673396])) (TableTree.leaf (#[5999993,10673396,10673396])))) (TableTree.node 868 (TableTree.node 867 (TableTree.leaf (#[5905790,10673396,10673396])) (TableTree.leaf (#[5999993,10673396,10673396]))) (TableTree.node 869 (TableTree.leaf (#[5999994,10673396,10673396])) (TableTree.leaf (#[5905793,10673396,10673396])))))))) (TableTree.node 899 (TableTree.node 884 (TableTree.node 877 (TableTree.node 873 (TableTree.node 871 (TableTree.leaf (#[5905793,10673396,10673396])) (TableTree.node 872 (TableTree.leaf (#[5999996,10673396,10673396])) (TableTree.leaf (#[5905790,10673396,10673396])))) (TableTree.node 875 (TableTree.node 874 (TableTree.leaf (#[5999993,10673396,10673396])) (TableTree.leaf (#[5905791,10673396,10673396]))) (TableTree.node 876 (TableTree.leaf (#[5999991,10673396,10673396])) (TableTree.leaf (#[5999992,10673396,10673396]))))) (TableTree.node 880 (TableTree.node 878 (TableTree.leaf (#[5905792,10673396,10673396])) (TableTree.node 879 (TableTree.leaf (#[5999992,10673396,10673396])) (TableTree.leaf (#[5905792,10673396,10673396])))) (TableTree.node 882 (TableTree.node 881 (TableTree.leaf (#[5999996,10673396,10673396])) (TableTree.leaf (#[5999993,10673396,10673396]))) (TableTree.node 883 (TableTree.leaf (#[5905790,10673396,10673396])) (TableTree.leaf (#[5905791,10673396,10673396])))))) (TableTree.node 891 (TableTree.node 887 (TableTree.node 885 (TableTree.leaf (#[5999994,10673396,10673396])) (TableTree.node 886 (TableTree.leaf (#[5999996,16859396,10673396])) (TableTree.leaf (#[16859396,5905793,10673396])))) (TableTree.node 889 (TableTree.node 888 (TableTree.leaf (#[16859396,5905793,10673396])) (TableTree.leaf (#[16859396,5905792,10673396]))) (TableTree.node 890 (TableTree.leaf (#[16859396,5905793,10673396])) (TableTree.leaf (#[16859396,5905793,10673396]))))) (TableTree.node 895 (TableTree.node 893 (TableTree.node 892 (TableTree.leaf (#[16859396,5905792,10673396])) (TableTree.leaf (#[16859396,5905793,10673396]))) (TableTree.node 894 (TableTree.leaf (#[16859396,5905793,10673396])) (TableTree.leaf (#[5999990,16859396,10673396])))) (TableTree.node 897 (TableTree.node 896 (TableTree.leaf (#[16859396,5905787,10673396])) (TableTree.leaf (#[16859396,5905790,10673396]))) (TableTree.node 898 (TableTree.leaf (#[16859396,5905787,10673396])) (TableTree.leaf (#[16859396,5905793,10673396]))))))) (TableTree.node 914 (TableTree.node 906 (TableTree.node 902 (TableTree.node 900 (TableTree.leaf (#[16859396,5905789,10673396])) (TableTree.node 901 (TableTree.leaf (#[16859396,5905790,10673396])) (TableTree.leaf (#[16859396,5905790,10673396])))) (TableTree.node 904 (TableTree.node 903 (TableTree.leaf (#[16859396,5905796,10673396])) (TableTree.leaf (#[5999995,16859396,10673396]))) (TableTree.node 905 (TableTree.leaf (#[16859396,5905792,10673396])) (TableTree.leaf (#[16859396,5905792,10673396]))))) (TableTree.node 910 (TableTree.node 908 (TableTree.node 907 (TableTree.leaf (#[16859396,5905792,10673396])) (TableTree.leaf (#[16859396,5905793,10673396]))) (TableTree.node 909 (TableTree.leaf (#[16859396,5905793,10673396])) (TableTree.leaf (#[16859396,5905793,10673396])))) (TableTree.node 912 (TableTree.node 911 (TableTree.leaf (#[16859396,5905794,10673396])) (TableTree.leaf (#[16859396,5905794,10673396]))) (TableTree.node 913 (TableTree.leaf (#[16859396,5999990,10673396])) (TableTree.leaf (#[16859396,5999990,10673396])))))) (TableTree.node 921 (TableTree.node 917 (TableTree.node 915 (TableTree.leaf (#[16859396,5999990,10673396])) (TableTree.node 916 (TableTree.leaf (#[16859396,5999990,10673396])) (TableTree.leaf (#[16859396,5999990,10673396])))) (TableTree.node 919 (TableTree.node 918 (TableTree.leaf (#[16859396,5999990,10673396])) (TableTree.leaf (#[16859396,5999990,10673396]))) (TableTree.node 920 (TableTree.leaf (#[16859396,5999990,10673396])) (TableTree.leaf (#[16859396,5999990,10673396]))))) (TableTree.node 925 (TableTree.node 923 (TableTree.node 922 (TableTree.leaf (#[5999993,16859396,10673396])) (TableTree.leaf (#[16859396,5905790,10673396]))) (TableTree.node 924 (TableTree.leaf (#[5999993,16859396,10673396])) (TableTree.leaf (#[16859396,5905790,10673396])))) (TableTree.node 927 (TableTree.node 926 (TableTree.leaf (#[5999993,16859396,10673396])) (TableTree.leaf (#[16859396,5905790,10673396]))) (TableTree.node 928 (TableTree.leaf (#[16859396,5905791,10673396])) (TableTree.leaf (#[16859396,5905791,10673396]))))))))))))
private def hAt (i : ℕ) : (Array (ℤ)) := if i < 929 then TableTree.lookup hAtTree i else #[]
private def destAtTree : TableTree ((Array ℕ)) := (TableTree.node 464 (TableTree.node 232 (TableTree.node 116 (TableTree.node 58 (TableTree.node 29 (TableTree.node 14 (TableTree.node 7 (TableTree.node 3 (TableTree.node 1 (TableTree.leaf (#[0,0,0,1,0,0,0,0,0,0,0,0])) (TableTree.node 2 (TableTree.leaf (#[2,0,0,3,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[4,0,0,5,0,0,0,0,0,0,0,0])))) (TableTree.node 5 (TableTree.node 4 (TableTree.leaf (#[6,0,0,7,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[8,0,0,0,0,0,9,0,0,0,0,0]))) (TableTree.node 6 (TableTree.leaf (#[0,0,0,0,0,0,11,0,0,10,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,13,0,0,12,0,0]))))) (TableTree.node 10 (TableTree.node 8 (TableTree.leaf (#[0,0,0,0,0,0,15,0,0,14,0,0])) (TableTree.node 9 (TableTree.leaf (#[0,0,0,0,0,0,17,0,0,16,0,0])) (TableTree.leaf (#[18,0,0,19,0,0,0,0,0,0,0,0])))) (TableTree.node 12 (TableTree.node 11 (TableTree.leaf (#[20,0,0,21,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[22,0,0,23,0,0,0,0,0,0,0,0]))) (TableTree.node 13 (TableTree.leaf (#[24,0,0,25,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[26,0,0,0,0,0,27,28,0,0,0,0])))))) (TableTree.node 21 (TableTree.node 17 (TableTree.node 15 (TableTree.leaf (#[0,0,0,0,0,0,31,32,0,29,30,0])) (TableTree.node 16 (TableTree.leaf (#[0,0,0,0,0,0,35,36,0,33,34,0])) (TableTree.leaf (#[0,0,0,0,0,0,39,40,0,37,38,0])))) (TableTree.node 19 (TableTree.node 18 (TableTree.leaf (#[0,0,0,0,0,0,43,44,0,41,42,0])) (TableTree.leaf (#[45,0,0,46,0,0,0,0,0,0,0,0]))) (TableTree.node 20 (TableTree.leaf (#[47,0,0,48,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[49,0,0,50,0,0,0,0,0,0,0,0]))))) (TableTree.node 25 (TableTree.node 23 (TableTree.node 22 (TableTree.leaf (#[51,0,0,52,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[53,0,0,0,0,0,54,55,0,0,0,0]))) (TableTree.node 24 (TableTree.leaf (#[0,0,0,0,0,0,58,59,0,56,57,0])) (TableTree.leaf (#[0,0,0,0,0,0,62,63,0,60,61,0])))) (TableTree.node 27 (TableTree.node 26 (TableTree.leaf (#[0,0,0,0,0,0,66,67,0,64,65,0])) (TableTree.leaf (#[0,0,0,0,0,0,70,71,0,68,69,0]))) (TableTree.node 28 (TableTree.leaf (#[72,0,0,73,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[74,0,0,75,0,0,0,0,0,0,0,0]))))))) (TableTree.node 43 (TableTree.node 36 (TableTree.node 32 (TableTree.node 30 (TableTree.leaf (#[76,0,0,77,0,0,0,0,0,0,0,0])) (TableTree.node 31 (TableTree.leaf (#[78,0,0,79,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[80,0,0,81,0,0,0,0,0,0,0,0])))) (TableTree.node 34 (TableTree.node 33 (TableTree.leaf (#[82,0,0,83,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[84,0,0,85,0,0,0,0,0,0,0,0]))) (TableTree.node 35 (TableTree.leaf (#[86,0,0,87,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[88,0,0,0,0,0,89,90,0,0,0,0]))))) (TableTree.node 39 (TableTree.node 37 (TableTree.leaf (#[91,0,0,0,0,0,92,0,0,0,0,0])) (TableTree.node 38 (TableTree.leaf (#[0,0,0,0,0,0,95,96,0,93,94,0])) (TableTree.leaf (#[0,0,0,0,0,0,98,0,0,97,0,0])))) (TableTree.node 41 (TableTree.node 40 (TableTree.leaf (#[0,0,0,0,0,0,101,102,0,99,100,0])) (TableTree.leaf (#[0,0,0,0,0,0,104,0,0,103,0,0]))) (TableTree.node 42 (TableTree.leaf (#[0,0,0,0,0,0,107,108,0,105,106,0])) (TableTree.leaf (#[0,0,0,0,0,0,110,0,0,109,0,0])))))) (TableTree.node 50 (TableTree.node 46 (TableTree.node 44 (TableTree.leaf (#[0,0,0,0,0,0,113,114,0,111,112,0])) (TableTree.node 45 (TableTree.leaf (#[0,0,0,0,0,0,116,0,0,115,0,0])) (TableTree.leaf (#[117,0,0,118,0,0,0,0,0,0,0,0])))) (TableTree.node 48 (TableTree.node 47 (TableTree.leaf (#[119,0,0,120,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[121,0,0,122,0,0,0,0,0,0,0,0]))) (TableTree.node 49 (TableTree.leaf (#[123,0,0,124,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[125,0,0,0,0,0,126,127,0,0,0,0]))))) (TableTree.node 54 (TableTree.node 52 (TableTree.node 51 (TableTree.leaf (#[0,0,0,0,0,0,130,131,0,128,129,0])) (TableTree.leaf (#[0,0,0,0,0,0,134,135,0,132,133,0]))) (TableTree.node 53 (TableTree.leaf (#[0,0,0,0,0,0,138,139,0,136,137,0])) (TableTree.leaf (#[0,0,0,0,0,0,142,143,0,140,141,0])))) (TableTree.node 56 (TableTree.node 55 (TableTree.leaf (#[144,0,0,145,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[146,0,0,147,0,0,0,0,0,0,0,0]))) (TableTree.node 57 (TableTree.leaf (#[148,0,0,149,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[150,0,0,151,0,0,0,0,0,0,0,0])))))))) (TableTree.node 87 (TableTree.node 72 (TableTree.node 65 (TableTree.node 61 (TableTree.node 59 (TableTree.leaf (#[152,0,0,153,0,0,0,0,0,0,0,0])) (TableTree.node 60 (TableTree.leaf (#[154,0,0,155,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[156,0,0,157,0,0,0,0,0,0,0,0])))) (TableTree.node 63 (TableTree.node 62 (TableTree.leaf (#[158,0,0,159,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[160,0,0,0,0,0,161,0,0,0,0,0]))) (TableTree.node 64 (TableTree.leaf (#[162,0,0,0,0,0,163,164,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,166,0,0,165,0,0]))))) (TableTree.node 68 (TableTree.node 66 (TableTree.leaf (#[0,0,0,0,0,0,169,170,0,167,168,0])) (TableTree.node 67 (TableTree.leaf (#[0,0,0,0,0,0,172,0,0,171,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,175,176,0,173,174,0])))) (TableTree.node 70 (TableTree.node 69 (TableTree.leaf (#[0,0,0,0,0,0,178,0,0,177,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,181,182,0,179,180,0]))) (TableTree.node 71 (TableTree.leaf (#[0,0,0,0,0,0,184,0,0,183,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,187,188,0,185,186,0])))))) (TableTree.node 79 (TableTree.node 75 (TableTree.node 73 (TableTree.leaf (#[189,0,0,190,0,0,0,0,0,0,0,0])) (TableTree.node 74 (TableTree.leaf (#[191,0,0,192,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[193,0,0,194,0,0,0,0,0,0,0,0])))) (TableTree.node 77 (TableTree.node 76 (TableTree.leaf (#[195,0,0,196,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[197,0,0,198,0,0,0,0,0,0,0,0]))) (TableTree.node 78 (TableTree.leaf (#[199,0,0,200,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[201,0,0,202,0,0,0,0,0,0,0,0]))))) (TableTree.node 83 (TableTree.node 81 (TableTree.node 80 (TableTree.leaf (#[203,0,0,204,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[205,0,0,0,0,0,206,207,0,0,0,0]))) (TableTree.node 82 (TableTree.leaf (#[0,0,0,0,0,0,210,211,0,208,209,0])) (TableTree.leaf (#[212,0,0,0,0,0,213,0,0,0,0,0])))) (TableTree.node 85 (TableTree.node 84 (TableTree.leaf (#[0,0,0,0,0,0,215,0,0,214,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,218,219,0,216,217,0]))) (TableTree.node 86 (TableTree.leaf (#[0,0,0,0,0,0,222,223,0,220,221,0])) (TableTree.leaf (#[0,0,0,0,0,0,225,0,0,224,0,0]))))))) (TableTree.node 101 (TableTree.node 94 (TableTree.node 90 (TableTree.node 88 (TableTree.leaf (#[0,0,0,0,0,0,227,0,0,226,0,0])) (TableTree.node 89 (TableTree.leaf (#[0,0,0,0,0,0,230,231,0,228,229,0])) (TableTree.leaf (#[232,233,0,234,235,0,0,0,0,0,0,0])))) (TableTree.node 92 (TableTree.node 91 (TableTree.leaf (#[236,0,0,237,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,239,0,0,238,0,0]))) (TableTree.node 93 (TableTree.leaf (#[240,0,0,241,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[242,243,0,244,245,0,0,0,0,0,0,0]))))) (TableTree.node 97 (TableTree.node 95 (TableTree.leaf (#[246,0,0,247,0,0,0,0,0,0,0,0])) (TableTree.node 96 (TableTree.leaf (#[248,249,0,250,251,0,0,0,0,0,0,0])) (TableTree.leaf (#[252,0,0,253,0,0,0,0,0,0,0,0])))) (TableTree.node 99 (TableTree.node 98 (TableTree.leaf (#[254,0,0,255,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[256,0,0,257,0,0,0,0,0,0,0,0]))) (TableTree.node 100 (TableTree.leaf (#[258,259,0,260,261,0,0,0,0,0,0,0])) (TableTree.leaf (#[262,0,0,263,0,0,0,0,0,0,0,0])))))) (TableTree.node 108 (TableTree.node 104 (TableTree.node 102 (TableTree.leaf (#[264,265,0,0,0,0,266,0,0,0,0,0])) (TableTree.node 103 (TableTree.leaf (#[267,0,0,0,0,0,268,269,0,0,0,0])) (TableTree.leaf (#[270,0,0,271,0,0,0,0,0,0,0,0])))) (TableTree.node 106 (TableTree.node 105 (TableTree.leaf (#[272,0,0,0,0,0,273,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,275,0,0,274,0,0]))) (TableTree.node 107 (TableTree.leaf (#[0,0,0,0,0,0,278,279,0,276,277,0])) (TableTree.leaf (#[0,0,0,0,0,0,281,0,0,280,0,0]))))) (TableTree.node 112 (TableTree.node 110 (TableTree.node 109 (TableTree.leaf (#[0,0,0,0,0,0,284,285,0,282,283,0])) (TableTree.leaf (#[0,0,0,0,0,0,287,0,0,286,0,0]))) (TableTree.node 111 (TableTree.leaf (#[0,0,0,0,0,0,289,0,0,288,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,291,0,0,290,0,0])))) (TableTree.node 114 (TableTree.node 113 (TableTree.leaf (#[0,0,0,0,0,0,294,295,0,292,293,0])) (TableTree.leaf (#[0,0,0,0,0,0,297,0,0,296,0,0]))) (TableTree.node 115 (TableTree.leaf (#[0,0,0,0,0,0,300,301,0,298,299,0])) (TableTree.leaf (#[0,0,0,0,0,0,303,0,0,302,0,0]))))))))) (TableTree.node 174 (TableTree.node 145 (TableTree.node 130 (TableTree.node 123 (TableTree.node 119 (TableTree.node 117 (TableTree.leaf (#[0,0,0,0,0,0,305,0,0,304,0,0])) (TableTree.node 118 (TableTree.leaf (#[164,0,0,168,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[170,0,0,174,0,0,0,0,0,0,0,0])))) (TableTree.node 121 (TableTree.node 120 (TableTree.leaf (#[176,0,0,180,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[182,0,0,186,0,0,0,0,0,0,0,0]))) (TableTree.node 122 (TableTree.leaf (#[188,0,0,0,0,0,306,307,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,310,311,0,308,309,0]))))) (TableTree.node 126 (TableTree.node 124 (TableTree.leaf (#[0,0,0,0,0,0,314,315,0,312,313,0])) (TableTree.node 125 (TableTree.leaf (#[0,0,0,0,0,0,318,319,0,316,317,0])) (TableTree.leaf (#[0,0,0,0,0,0,322,323,0,320,321,0])))) (TableTree.node 128 (TableTree.node 127 (TableTree.leaf (#[324,325,0,326,327,0,0,0,0,0,0,0])) (TableTree.leaf (#[328,0,0,329,0,0,0,0,0,0,0,0]))) (TableTree.node 129 (TableTree.leaf (#[330,331,0,332,333,0,0,0,0,0,0,0])) (TableTree.leaf (#[334,0,0,335,0,0,0,0,0,0,0,0])))))) (TableTree.node 137 (TableTree.node 133 (TableTree.node 131 (TableTree.leaf (#[336,337,0,338,339,0,0,0,0,0,0,0])) (TableTree.node 132 (TableTree.leaf (#[340,0,0,341,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[342,343,0,344,345,0,0,0,0,0,0,0])))) (TableTree.node 135 (TableTree.node 134 (TableTree.leaf (#[346,0,0,347,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[348,349,0,0,0,0,350,0,0,0,0,0]))) (TableTree.node 136 (TableTree.leaf (#[351,0,0,0,0,0,163,164,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,353,0,0,352,0,0]))))) (TableTree.node 141 (TableTree.node 139 (TableTree.node 138 (TableTree.leaf (#[0,0,0,0,0,0,169,170,0,167,168,0])) (TableTree.leaf (#[0,0,0,0,0,0,355,0,0,354,0,0]))) (TableTree.node 140 (TableTree.leaf (#[0,0,0,0,0,0,175,176,0,173,174,0])) (TableTree.leaf (#[0,0,0,0,0,0,357,0,0,356,0,0])))) (TableTree.node 143 (TableTree.node 142 (TableTree.leaf (#[0,0,0,0,0,0,181,182,0,179,180,0])) (TableTree.leaf (#[0,0,0,0,0,0,359,0,0,358,0,0]))) (TableTree.node 144 (TableTree.leaf (#[0,0,0,0,0,0,187,188,0,185,186,0])) (TableTree.leaf (#[360,0,0,361,0,0,0,0,0,0,0,0]))))))) (TableTree.node 159 (TableTree.node 152 (TableTree.node 148 (TableTree.node 146 (TableTree.leaf (#[362,0,0,363,0,0,0,0,0,0,0,0])) (TableTree.node 147 (TableTree.leaf (#[307,0,0,309,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[311,0,0,313,0,0,0,0,0,0,0,0])))) (TableTree.node 150 (TableTree.node 149 (TableTree.leaf (#[364,0,0,365,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[366,0,0,367,0,0,0,0,0,0,0,0]))) (TableTree.node 151 (TableTree.leaf (#[315,0,0,317,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[319,0,0,321,0,0,0,0,0,0,0,0]))))) (TableTree.node 155 (TableTree.node 153 (TableTree.leaf (#[368,0,0,0,0,0,369,0,0,0,0,0])) (TableTree.node 154 (TableTree.leaf (#[0,0,0,0,0,0,371,0,0,370,0,0])) (TableTree.leaf (#[323,0,0,0,0,0,306,307,0,0,0,0])))) (TableTree.node 157 (TableTree.node 156 (TableTree.leaf (#[0,0,0,0,0,0,310,311,0,308,309,0])) (TableTree.leaf (#[0,0,0,0,0,0,364,0,0,372,0,0]))) (TableTree.node 158 (TableTree.leaf (#[0,0,0,0,0,0,366,0,0,373,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,314,315,0,312,313,0])))))) (TableTree.node 166 (TableTree.node 162 (TableTree.node 160 (TableTree.leaf (#[0,0,0,0,0,0,318,319,0,316,317,0])) (TableTree.node 161 (TableTree.leaf (#[0,0,0,0,0,0,374,0,0,367,0,0])) (TableTree.leaf (#[375,0,0,376,0,0,0,0,0,0,0,0])))) (TableTree.node 164 (TableTree.node 163 (TableTree.leaf (#[0,0,0,0,0,0,322,323,0,320,321,0])) (TableTree.leaf (#[821,822,0,379,380,0,0,0,0,0,0,0]))) (TableTree.node 165 (TableTree.leaf (#[823,0,0,913,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[825,0,0,826,0,0,0,0,0,0,0,0]))))) (TableTree.node 170 (TableTree.node 168 (TableTree.node 167 (TableTree.leaf (#[385,0,0,386,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[827,828,0,829,906,0,0,0,0,0,0,0]))) (TableTree.node 169 (TableTree.leaf (#[831,0,0,915,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[833,834,0,835,908,0,0,0,0,0,0,0])))) (TableTree.node 172 (TableTree.node 171 (TableTree.leaf (#[837,0,0,917,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[839,0,0,400,0,0,0,0,0,0,0,0]))) (TableTree.node 173 (TableTree.leaf (#[401,0,0,0,0,0,402,0,0,0,0,0])) (TableTree.leaf (#[840,841,0,901,910,0,0,0,0,0,0,0])))))))) (TableTree.node 203 (TableTree.node 188 (TableTree.node 181 (TableTree.node 177 (TableTree.node 175 (TableTree.leaf (#[844,0,0,919,0,0,0,0,0,0,0,0])) (TableTree.node 176 (TableTree.leaf (#[846,847,0,0,0,0,903,0,0,0,0,0])) (TableTree.leaf (#[848,0,0,0,0,0,894,912,0,0,0,0])))) (TableTree.node 179 (TableTree.node 178 (TableTree.leaf (#[0,0,0,0,0,0,887,0,0,849,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,385,0,0,826,0,0]))) (TableTree.node 180 (TableTree.leaf (#[0,0,0,0,0,0,905,0,0,851,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,896,914,0,853,824,0]))))) (TableTree.node 184 (TableTree.node 182 (TableTree.leaf (#[0,0,0,0,0,0,417,0,0,830,0,0])) (TableTree.node 183 (TableTree.leaf (#[0,0,0,0,0,0,898,916,0,854,832,0])) (TableTree.leaf (#[0,0,0,0,0,0,420,0,0,419,0,0])))) (TableTree.node 186 (TableTree.node 185 (TableTree.leaf (#[0,0,0,0,0,0,422,0,0,421,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,909,0,0,855,0,0]))) (TableTree.node 187 (TableTree.leaf (#[0,0,0,0,0,0,900,918,0,857,838,0])) (TableTree.leaf (#[0,0,0,0,0,0,911,0,0,859,0,0])))))) (TableTree.node 195 (TableTree.node 191 (TableTree.node 189 (TableTree.leaf (#[0,0,0,0,0,0,902,920,0,842,845,0])) (TableTree.node 190 (TableTree.leaf (#[823,0,0,913,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[831,0,0,915,0,0,0,0,0,0,0,0])))) (TableTree.node 193 (TableTree.node 192 (TableTree.leaf (#[837,0,0,917,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[844,0,0,919,0,0,0,0,0,0,0,0]))) (TableTree.node 194 (TableTree.leaf (#[861,0,0,430,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[431,0,0,432,0,0,0,0,0,0,0,0]))))) (TableTree.node 199 (TableTree.node 197 (TableTree.node 196 (TableTree.leaf (#[433,0,0,434,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[420,0,0,435,0,0,0,0,0,0,0,0]))) (TableTree.node 198 (TableTree.leaf (#[848,0,0,0,0,0,894,912,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,896,914,0,853,824,0])))) (TableTree.node 201 (TableTree.node 200 (TableTree.leaf (#[0,0,0,0,0,0,898,916,0,854,832,0])) (TableTree.leaf (#[0,0,0,0,0,0,900,918,0,857,838,0]))) (TableTree.node 202 (TableTree.leaf (#[862,0,0,0,0,0,885,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,437,0,0,430,0,0]))))))) (TableTree.node 217 (TableTree.node 210 (TableTree.node 206 (TableTree.node 204 (TableTree.leaf (#[0,0,0,0,0,0,385,0,0,826,0,0])) (TableTree.node 205 (TableTree.leaf (#[0,0,0,0,0,0,420,0,0,419,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,902,920,0,842,845,0])))) (TableTree.node 208 (TableTree.node 207 (TableTree.leaf (#[821,822,0,379,380,0,0,0,0,0,0,0])) (TableTree.leaf (#[823,0,0,913,0,0,0,0,0,0,0,0]))) (TableTree.node 209 (TableTree.leaf (#[827,828,0,829,906,0,0,0,0,0,0,0])) (TableTree.leaf (#[831,0,0,915,0,0,0,0,0,0,0,0]))))) (TableTree.node 213 (TableTree.node 211 (TableTree.leaf (#[833,834,0,835,908,0,0,0,0,0,0,0])) (TableTree.node 212 (TableTree.leaf (#[837,0,0,917,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,422,0,0,435,0,0])))) (TableTree.node 215 (TableTree.node 214 (TableTree.leaf (#[402,0,0,376,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[438,0,0,432,0,0,0,0,0,0,0,0]))) (TableTree.node 216 (TableTree.leaf (#[433,0,0,434,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[840,841,0,901,910,0,0,0,0,0,0,0])))))) (TableTree.node 224 (TableTree.node 220 (TableTree.node 218 (TableTree.leaf (#[844,0,0,919,0,0,0,0,0,0,0,0])) (TableTree.node 219 (TableTree.leaf (#[846,847,0,0,0,0,439,0,0,0,0,0])) (TableTree.leaf (#[848,0,0,0,0,0,440,441,0,0,0,0])))) (TableTree.node 222 (TableTree.node 221 (TableTree.leaf (#[0,0,0,0,0,0,443,0,0,442,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,446,447,0,444,445,0]))) (TableTree.node 223 (TableTree.leaf (#[0,0,0,0,0,0,449,0,0,448,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,452,453,0,450,451,0]))))) (TableTree.node 228 (TableTree.node 226 (TableTree.node 225 (TableTree.leaf (#[863,0,0,892,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[862,0,0,0,0,0,456,0,0,0,0,0]))) (TableTree.node 227 (TableTree.leaf (#[0,0,0,0,0,0,458,0,0,457,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,460,0,0,459,0,0])))) (TableTree.node 230 (TableTree.node 229 (TableTree.leaf (#[0,0,0,0,0,0,462,0,0,461,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,465,466,0,463,464,0]))) (TableTree.node 231 (TableTree.leaf (#[0,0,0,0,0,0,468,0,0,467,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,471,472,0,469,470,0])))))))))) (TableTree.node 348 (TableTree.node 290 (TableTree.node 261 (TableTree.node 246 (TableTree.node 239 (TableTree.node 235 (TableTree.node 233 (TableTree.leaf (#[473,474,0,475,476,0,0,0,0,0,0,0])) (TableTree.node 234 (TableTree.leaf (#[477,0,0,478,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[479,480,0,481,482,0,0,0,0,0,0,0])))) (TableTree.node 237 (TableTree.node 236 (TableTree.leaf (#[483,0,0,484,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[485,0,0,486,0,0,0,0,0,0,0,0]))) (TableTree.node 238 (TableTree.leaf (#[487,0,0,488,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,490,0,0,489,0,0]))))) (TableTree.node 242 (TableTree.node 240 (TableTree.leaf (#[0,0,0,0,0,0,492,0,0,491,0,0])) (TableTree.node 241 (TableTree.leaf (#[493,0,0,494,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[495,0,0,496,0,0,0,0,0,0,0,0])))) (TableTree.node 244 (TableTree.node 243 (TableTree.leaf (#[497,498,0,499,500,0,0,0,0,0,0,0])) (TableTree.leaf (#[501,0,0,502,0,0,0,0,0,0,0,0]))) (TableTree.node 245 (TableTree.leaf (#[503,504,0,505,506,0,0,0,0,0,0,0])) (TableTree.leaf (#[507,0,0,508,0,0,0,0,0,0,0,0])))))) (TableTree.node 253 (TableTree.node 249 (TableTree.node 247 (TableTree.leaf (#[509,0,0,510,0,0,0,0,0,0,0,0])) (TableTree.node 248 (TableTree.leaf (#[511,0,0,512,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[513,514,0,0,0,0,515,0,0,0,0,0])))) (TableTree.node 251 (TableTree.node 250 (TableTree.leaf (#[516,0,0,0,0,0,360,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,518,0,0,517,0,0]))) (TableTree.node 252 (TableTree.leaf (#[0,0,0,0,0,0,520,0,0,519,0,0])) (TableTree.leaf (#[521,0,0,0,0,0,306,307,0,0,0,0]))))) (TableTree.node 257 (TableTree.node 255 (TableTree.node 254 (TableTree.leaf (#[0,0,0,0,0,0,310,311,0,308,309,0])) (TableTree.leaf (#[522,0,0,523,0,0,0,0,0,0,0,0]))) (TableTree.node 256 (TableTree.leaf (#[524,0,0,525,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[526,0,0,0,0,0,369,0,0,0,0,0])))) (TableTree.node 259 (TableTree.node 258 (TableTree.leaf (#[0,0,0,0,0,0,371,0,0,370,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,528,0,0,527,0,0]))) (TableTree.node 260 (TableTree.leaf (#[0,0,0,0,0,0,364,0,0,372,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,530,0,0,529,0,0]))))))) (TableTree.node 275 (TableTree.node 268 (TableTree.node 264 (TableTree.node 262 (TableTree.leaf (#[0,0,0,0,0,0,531,0,0,365,0,0])) (TableTree.node 263 (TableTree.leaf (#[0,0,0,0,0,0,314,315,0,312,313,0])) (TableTree.leaf (#[0,0,0,0,0,0,318,319,0,316,317,0])))) (TableTree.node 266 (TableTree.node 265 (TableTree.leaf (#[0,0,0,0,0,0,533,0,0,532,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,535,0,0,534,0,0]))) (TableTree.node 267 (TableTree.leaf (#[536,0,0,537,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,322,323,0,320,321,0]))))) (TableTree.node 271 (TableTree.node 269 (TableTree.leaf (#[538,539,0,540,541,0,0,0,0,0,0,0])) (TableTree.node 270 (TableTree.leaf (#[542,0,0,543,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,545,0,0,544,0,0])))) (TableTree.node 273 (TableTree.node 272 (TableTree.leaf (#[0,0,0,0,0,0,547,0,0,546,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,549,0,0,548,0,0]))) (TableTree.node 274 (TableTree.leaf (#[550,0,0,551,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[552,0,0,553,0,0,0,0,0,0,0,0])))))) (TableTree.node 282 (TableTree.node 278 (TableTree.node 276 (TableTree.leaf (#[554,0,0,555,0,0,0,0,0,0,0,0])) (TableTree.node 277 (TableTree.leaf (#[556,557,0,558,559,0,0,0,0,0,0,0])) (TableTree.leaf (#[560,0,0,561,0,0,0,0,0,0,0,0])))) (TableTree.node 280 (TableTree.node 279 (TableTree.leaf (#[562,563,0,564,565,0,0,0,0,0,0,0])) (TableTree.leaf (#[566,0,0,567,0,0,0,0,0,0,0,0]))) (TableTree.node 281 (TableTree.leaf (#[568,0,0,569,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[570,0,0,0,0,0,571,0,0,0,0,0]))))) (TableTree.node 286 (TableTree.node 284 (TableTree.node 283 (TableTree.leaf (#[572,573,0,574,575,0,0,0,0,0,0,0])) (TableTree.leaf (#[576,0,0,577,0,0,0,0,0,0,0,0]))) (TableTree.node 285 (TableTree.leaf (#[578,579,0,0,0,0,580,0,0,0,0,0])) (TableTree.leaf (#[581,0,0,0,0,0,582,583,0,0,0,0])))) (TableTree.node 288 (TableTree.node 287 (TableTree.leaf (#[584,0,0,585,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[586,0,0,587,0,0,0,0,0,0,0,0]))) (TableTree.node 289 (TableTree.leaf (#[588,0,0,589,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[590,0,0,0,0,0,571,0,0,0,0,0])))))))) (TableTree.node 319 (TableTree.node 304 (TableTree.node 297 (TableTree.node 293 (TableTree.node 291 (TableTree.leaf (#[0,0,0,0,0,0,592,0,0,591,0,0])) (TableTree.node 292 (TableTree.leaf (#[0,0,0,0,0,0,594,0,0,593,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,596,0,0,595,0,0])))) (TableTree.node 295 (TableTree.node 294 (TableTree.leaf (#[0,0,0,0,0,0,599,600,0,597,598,0])) (TableTree.leaf (#[0,0,0,0,0,0,602,0,0,601,0,0]))) (TableTree.node 296 (TableTree.leaf (#[0,0,0,0,0,0,605,606,0,603,604,0])) (TableTree.leaf (#[0,0,0,0,0,0,608,0,0,607,0,0]))))) (TableTree.node 300 (TableTree.node 298 (TableTree.leaf (#[0,0,0,0,0,0,610,0,0,609,0,0])) (TableTree.node 299 (TableTree.leaf (#[0,0,0,0,0,0,612,0,0,611,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,615,616,0,613,614,0])))) (TableTree.node 302 (TableTree.node 301 (TableTree.leaf (#[0,0,0,0,0,0,618,0,0,617,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,621,622,0,619,620,0]))) (TableTree.node 303 (TableTree.leaf (#[0,0,0,0,0,0,624,0,0,623,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,626,0,0,625,0,0])))))) (TableTree.node 311 (TableTree.node 307 (TableTree.node 305 (TableTree.leaf (#[0,0,0,0,0,0,628,0,0,627,0,0])) (TableTree.node 306 (TableTree.leaf (#[0,0,0,0,0,0,630,0,0,629,0,0])) (TableTree.leaf (#[163,350,0,631,632,0,0,0,0,0,0,0])))) (TableTree.node 309 (TableTree.node 308 (TableTree.leaf (#[164,0,0,168,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[169,633,0,634,354,0,0,0,0,0,0,0]))) (TableTree.node 310 (TableTree.leaf (#[170,0,0,174,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[175,635,0,636,637,0,0,0,0,0,0,0]))))) (TableTree.node 315 (TableTree.node 313 (TableTree.node 312 (TableTree.leaf (#[176,0,0,180,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[638,639,0,185,640,0,0,0,0,0,0,0]))) (TableTree.node 314 (TableTree.leaf (#[182,0,0,186,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[187,641,0,0,0,0,903,0,0,0,0,0])))) (TableTree.node 317 (TableTree.node 316 (TableTree.leaf (#[188,0,0,0,0,0,894,912,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,905,0,0,851,0,0]))) (TableTree.node 318 (TableTree.leaf (#[0,0,0,0,0,0,896,914,0,853,824,0])) (TableTree.leaf (#[0,0,0,0,0,0,417,0,0,830,0,0]))))))) (TableTree.node 333 (TableTree.node 326 (TableTree.node 322 (TableTree.node 320 (TableTree.leaf (#[0,0,0,0,0,0,898,916,0,854,832,0])) (TableTree.node 321 (TableTree.leaf (#[0,0,0,0,0,0,909,0,0,855,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,900,918,0,857,838,0])))) (TableTree.node 324 (TableTree.node 323 (TableTree.leaf (#[0,0,0,0,0,0,911,0,0,859,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,902,920,0,842,845,0]))) (TableTree.node 325 (TableTree.leaf (#[642,643,0,644,645,0,0,0,0,0,0,0])) (TableTree.leaf (#[646,0,0,647,0,0,0,0,0,0,0,0]))))) (TableTree.node 329 (TableTree.node 327 (TableTree.leaf (#[648,649,0,650,651,0,0,0,0,0,0,0])) (TableTree.node 328 (TableTree.leaf (#[652,0,0,653,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[654,0,0,655,0,0,0,0,0,0,0,0])))) (TableTree.node 331 (TableTree.node 330 (TableTree.leaf (#[656,0,0,657,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[658,659,0,660,661,0,0,0,0,0,0,0]))) (TableTree.node 332 (TableTree.leaf (#[662,0,0,663,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[664,665,0,666,667,0,0,0,0,0,0,0])))))) (TableTree.node 340 (TableTree.node 336 (TableTree.node 334 (TableTree.leaf (#[668,0,0,669,0,0,0,0,0,0,0,0])) (TableTree.node 335 (TableTree.leaf (#[670,0,0,671,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[672,0,0,673,0,0,0,0,0,0,0,0])))) (TableTree.node 338 (TableTree.node 337 (TableTree.leaf (#[674,675,0,0,0,0,676,0,0,0,0,0])) (TableTree.leaf (#[677,0,0,0,0,0,193,0,0,0,0,0]))) (TableTree.node 339 (TableTree.leaf (#[0,0,0,0,0,0,679,0,0,678,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,681,0,0,680,0,0]))))) (TableTree.node 344 (TableTree.node 342 (TableTree.node 341 (TableTree.leaf (#[682,0,0,0,0,0,189,683,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,191,685,0,190,684,0]))) (TableTree.node 343 (TableTree.leaf (#[0,0,0,0,0,0,687,0,0,686,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,201,0,0,688,0,0])))) (TableTree.node 346 (TableTree.node 345 (TableTree.leaf (#[0,0,0,0,0,0,690,0,0,689,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,691,0,0,202,0,0]))) (TableTree.node 347 (TableTree.leaf (#[0,0,0,0,0,0,197,693,0,192,692,0])) (TableTree.leaf (#[0,0,0,0,0,0,199,695,0,198,694,0]))))))))) (TableTree.node 406 (TableTree.node 377 (TableTree.node 362 (TableTree.node 355 (TableTree.node 351 (TableTree.node 349 (TableTree.leaf (#[0,0,0,0,0,0,697,0,0,696,0,0])) (TableTree.node 350 (TableTree.leaf (#[0,0,0,0,0,0,699,0,0,698,0,0])) (TableTree.leaf (#[865,0,0,701,0,0,0,0,0,0,0,0])))) (TableTree.node 353 (TableTree.node 352 (TableTree.leaf (#[0,0,0,0,0,0,205,703,0,200,702,0])) (TableTree.leaf (#[866,0,0,923,0,0,0,0,0,0,0,0]))) (TableTree.node 354 (TableTree.leaf (#[706,0,0,707,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[868,0,0,709,0,0,0,0,0,0,0,0]))))) (TableTree.node 358 (TableTree.node 356 (TableTree.leaf (#[710,0,0,0,0,0,402,0,0,0,0,0])) (TableTree.node 357 (TableTree.leaf (#[0,0,0,0,0,0,887,0,0,849,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,385,0,0,826,0,0])))) (TableTree.node 360 (TableTree.node 359 (TableTree.leaf (#[0,0,0,0,0,0,839,0,0,869,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,712,0,0,400,0,0]))) (TableTree.node 361 (TableTree.leaf (#[713,0,0,714,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[715,0,0,716,0,0,0,0,0,0,0,0])))))) (TableTree.node 369 (TableTree.node 365 (TableTree.node 363 (TableTree.leaf (#[717,0,0,718,0,0,0,0,0,0,0,0])) (TableTree.node 364 (TableTree.leaf (#[719,0,0,720,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[721,0,0,0,0,0,885,0,0,0,0,0])))) (TableTree.node 367 (TableTree.node 366 (TableTree.leaf (#[0,0,0,0,0,0,437,0,0,430,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,385,0,0,826,0,0]))) (TableTree.node 368 (TableTree.leaf (#[0,0,0,0,0,0,420,0,0,419,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,422,0,0,435,0,0]))))) (TableTree.node 373 (TableTree.node 371 (TableTree.node 370 (TableTree.leaf (#[722,0,0,723,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[724,0,0,716,0,0,0,0,0,0,0,0]))) (TableTree.node 372 (TableTree.leaf (#[717,0,0,718,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[725,0,0,726,0,0,0,0,0,0,0,0])))) (TableTree.node 375 (TableTree.node 374 (TableTree.leaf (#[0,0,0,0,0,0,887,0,0,849,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,422,0,0,421,0,0]))) (TableTree.node 376 (TableTree.leaf (#[402,812,0,376,813,0,0,0,0,0,0,0])) (TableTree.leaf (#[438,814,0,432,815,0,0,0,0,0,0,0]))))))) (TableTree.node 391 (TableTree.node 384 (TableTree.node 380 (TableTree.node 378 (TableTree.leaf (#[821,822,812,379,380,813,0,0,0,0,0,0])) (TableTree.node 379 (TableTree.leaf (#[865,812,0,701,813,0,0,0,0,0,0,0])) (TableTree.leaf (#[727,728,814,729,730,815,0,0,0,0,0,0])))) (TableTree.node 382 (TableTree.node 381 (TableTree.leaf (#[731,814,0,732,815,0,0,0,0,0,0,0])) (TableTree.leaf (#[823,812,0,913,813,0,0,0,0,0,0,0]))) (TableTree.node 383 (TableTree.leaf (#[831,814,0,915,815,0,0,0,0,0,0,0])) (TableTree.leaf (#[870,816,0,890,817,0,0,0,0,0,0,0]))))) (TableTree.node 387 (TableTree.node 385 (TableTree.leaf (#[839,818,0,400,819,0,0,0,0,0,0,0])) (TableTree.node 386 (TableTree.leaf (#[401,820,0,0,0,0,402,812,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,438,814,0,735,813,0])))) (TableTree.node 389 (TableTree.node 388 (TableTree.leaf (#[833,834,816,835,908,817,0,0,0,0,0,0])) (TableTree.leaf (#[872,816,0,925,817,0,0,0,0,0,0,0]))) (TableTree.node 390 (TableTree.leaf (#[858,856,818,738,739,819,0,0,0,0,0,0])) (TableTree.leaf (#[868,818,0,709,819,0,0,0,0,0,0,0])))))) (TableTree.node 398 (TableTree.node 394 (TableTree.node 392 (TableTree.leaf (#[837,816,0,917,817,0,0,0,0,0,0,0])) (TableTree.node 393 (TableTree.leaf (#[844,818,0,919,819,0,0,0,0,0,0,0])) (TableTree.leaf (#[846,847,820,0,0,0,903,812,0,0,0,0])))) (TableTree.node 396 (TableTree.node 395 (TableTree.leaf (#[874,820,0,0,0,0,885,812,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,742,814,0,875,813,0]))) (TableTree.node 397 (TableTree.leaf (#[0,0,0,0,0,0,437,814,0,876,813,0])) (TableTree.leaf (#[848,820,0,0,0,0,894,912,812,0,0,0]))))) (TableTree.node 402 (TableTree.node 400 (TableTree.node 399 (TableTree.leaf (#[0,0,0,0,0,0,896,914,814,853,824,813])) (TableTree.leaf (#[0,0,0,0,0,0,385,816,0,826,815,0]))) (TableTree.node 401 (TableTree.leaf (#[0,0,0,0,0,0,420,818,0,419,817,0])) (TableTree.leaf (#[0,0,0,0,0,0,422,820,0,435,819,0])))) (TableTree.node 404 (TableTree.node 403 (TableTree.leaf (#[402,812,0,376,813,0,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,907,816,0,877,815,0]))) (TableTree.node 405 (TableTree.leaf (#[0,0,0,0,0,0,889,816,0,879,815,0])) (TableTree.leaf (#[0,0,0,0,0,0,909,818,0,855,817,0])))))))) (TableTree.node 435 (TableTree.node 420 (TableTree.node 413 (TableTree.node 409 (TableTree.node 407 (TableTree.leaf (#[0,0,0,0,0,0,747,818,0,871,817,0])) (TableTree.node 408 (TableTree.leaf (#[0,0,0,0,0,0,898,916,816,854,832,815])) (TableTree.leaf (#[0,0,0,0,0,0,900,918,818,857,838,817])))) (TableTree.node 411 (TableTree.node 410 (TableTree.leaf (#[0,0,0,0,0,0,911,820,0,859,819,0])) (TableTree.leaf (#[0,0,0,0,0,0,893,820,0,864,819,0]))) (TableTree.node 412 (TableTree.leaf (#[0,0,0,0,0,0,902,920,820,842,845,819])) (TableTree.leaf (#[825,814,0,826,815,0,0,0,0,0,0,0]))))) (TableTree.node 416 (TableTree.node 414 (TableTree.leaf (#[385,816,0,386,817,0,0,0,0,0,0,0])) (TableTree.node 415 (TableTree.leaf (#[866,814,0,923,815,0,0,0,0,0,0,0])) (TableTree.leaf (#[706,816,0,707,817,0,0,0,0,0,0,0])))) (TableTree.node 418 (TableTree.node 417 (TableTree.leaf (#[827,828,814,829,906,815,0,0,0,0,0,0])) (TableTree.leaf (#[710,820,0,0,0,0,402,812,0,0,0,0]))) (TableTree.node 419 (TableTree.leaf (#[840,841,818,901,910,819,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,438,814,0,376,813,0])))))) (TableTree.node 427 (TableTree.node 423 (TableTree.node 421 (TableTree.leaf (#[0,0,0,0,0,0,433,816,0,432,815,0])) (TableTree.node 422 (TableTree.leaf (#[0,0,0,0,0,0,420,818,0,434,817,0])) (TableTree.leaf (#[0,0,0,0,0,0,422,820,0,435,819,0])))) (TableTree.node 425 (TableTree.node 424 (TableTree.leaf (#[0,0,0,0,0,0,887,814,0,849,813,0])) (TableTree.leaf (#[0,0,0,0,0,0,385,816,0,826,815,0]))) (TableTree.node 426 (TableTree.leaf (#[0,0,0,0,0,0,905,814,0,851,813,0])) (TableTree.leaf (#[0,0,0,0,0,0,417,816,0,830,815,0]))))) (TableTree.node 431 (TableTree.node 429 (TableTree.node 428 (TableTree.leaf (#[0,0,0,0,0,0,839,818,0,869,817,0])) (TableTree.leaf (#[0,0,0,0,0,0,712,820,0,400,819,0]))) (TableTree.node 430 (TableTree.leaf (#[861,812,0,430,813,0,0,0,0,0,0,0])) (TableTree.leaf (#[431,814,0,432,815,0,0,0,0,0,0,0])))) (TableTree.node 433 (TableTree.node 432 (TableTree.leaf (#[433,816,0,434,817,0,0,0,0,0,0,0])) (TableTree.leaf (#[420,818,0,435,819,0,0,0,0,0,0,0]))) (TableTree.node 434 (TableTree.leaf (#[422,820,0,0,0,0,402,812,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,438,814,0,376,813,0]))))))) (TableTree.node 449 (TableTree.node 442 (TableTree.node 438 (TableTree.node 436 (TableTree.leaf (#[0,0,0,0,0,0,420,818,0,434,817,0])) (TableTree.node 437 (TableTree.leaf (#[0,0,0,0,0,0,893,820,0,864,819,0])) (TableTree.leaf (#[749,816,0,434,817,0,0,0,0,0,0,0])))) (TableTree.node 440 (TableTree.node 439 (TableTree.leaf (#[433,816,0,434,817,0,0,0,0,0,0,0])) (TableTree.leaf (#[865,0,0,701,0,0,0,0,0,0,0,0]))) (TableTree.node 441 (TableTree.leaf (#[821,822,0,379,380,0,0,0,0,0,0,0])) (TableTree.leaf (#[823,0,0,913,0,0,0,0,0,0,0,0]))))) (TableTree.node 445 (TableTree.node 443 (TableTree.leaf (#[866,0,0,923,0,0,0,0,0,0,0,0])) (TableTree.node 444 (TableTree.leaf (#[706,0,0,707,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[827,828,0,829,906,0,0,0,0,0,0,0])))) (TableTree.node 447 (TableTree.node 446 (TableTree.leaf (#[831,0,0,915,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[833,834,0,835,908,0,0,0,0,0,0,0]))) (TableTree.node 448 (TableTree.leaf (#[837,0,0,917,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[868,0,0,709,0,0,0,0,0,0,0,0])))))) (TableTree.node 456 (TableTree.node 452 (TableTree.node 450 (TableTree.leaf (#[710,0,0,0,0,0,402,0,0,0,0,0])) (TableTree.node 451 (TableTree.leaf (#[840,841,0,901,910,0,0,0,0,0,0,0])) (TableTree.leaf (#[844,0,0,919,0,0,0,0,0,0,0,0])))) (TableTree.node 454 (TableTree.node 453 (TableTree.leaf (#[846,847,0,0,0,0,903,0,0,0,0,0])) (TableTree.leaf (#[848,0,0,0,0,0,894,912,0,0,0,0]))) (TableTree.node 455 (TableTree.leaf (#[0,0,0,0,0,0,889,816,0,879,815,0])) (TableTree.leaf (#[0,0,0,0,0,0,839,818,0,869,817,0]))))) (TableTree.node 460 (TableTree.node 458 (TableTree.node 457 (TableTree.leaf (#[861,0,0,430,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[825,0,0,826,0,0,0,0,0,0,0,0]))) (TableTree.node 459 (TableTree.leaf (#[385,0,0,386,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[839,0,0,400,0,0,0,0,0,0,0,0])))) (TableTree.node 462 (TableTree.node 461 (TableTree.leaf (#[401,0,0,0,0,0,402,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,887,0,0,849,0,0]))) (TableTree.node 463 (TableTree.leaf (#[0,0,0,0,0,0,385,0,0,826,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,905,0,0,851,0,0]))))))))))) (TableTree.node 696 (TableTree.node 580 (TableTree.node 522 (TableTree.node 493 (TableTree.node 478 (TableTree.node 471 (TableTree.node 467 (TableTree.node 465 (TableTree.leaf (#[0,0,0,0,0,0,896,914,0,853,824,0])) (TableTree.node 466 (TableTree.leaf (#[0,0,0,0,0,0,417,0,0,830,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,898,916,0,854,832,0])))) (TableTree.node 469 (TableTree.node 468 (TableTree.leaf (#[0,0,0,0,0,0,839,0,0,869,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,712,0,0,400,0,0]))) (TableTree.node 470 (TableTree.leaf (#[0,0,0,0,0,0,909,0,0,855,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,900,918,0,857,838,0]))))) (TableTree.node 474 (TableTree.node 472 (TableTree.leaf (#[0,0,0,0,0,0,911,0,0,859,0,0])) (TableTree.node 473 (TableTree.leaf (#[0,0,0,0,0,0,902,920,0,842,845,0])) (TableTree.leaf (#[163,350,0,631,632,0,0,0,0,0,0,0])))) (TableTree.node 476 (TableTree.node 475 (TableTree.leaf (#[750,0,0,751,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[752,753,0,754,755,0,0,0,0,0,0,0]))) (TableTree.node 477 (TableTree.leaf (#[756,0,0,757,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[713,0,0,714,0,0,0,0,0,0,0,0])))))) (TableTree.node 485 (TableTree.node 481 (TableTree.node 479 (TableTree.leaf (#[715,0,0,716,0,0,0,0,0,0,0,0])) (TableTree.node 480 (TableTree.leaf (#[758,759,0,760,761,0,0,0,0,0,0,0])) (TableTree.leaf (#[762,0,0,763,0,0,0,0,0,0,0,0])))) (TableTree.node 483 (TableTree.node 482 (TableTree.leaf (#[764,765,0,766,767,0,0,0,0,0,0,0])) (TableTree.leaf (#[768,0,0,769,0,0,0,0,0,0,0,0]))) (TableTree.node 484 (TableTree.leaf (#[717,0,0,718,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[719,0,0,720,0,0,0,0,0,0,0,0]))))) (TableTree.node 489 (TableTree.node 487 (TableTree.node 486 (TableTree.leaf (#[164,0,0,168,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[170,0,0,174,0,0,0,0,0,0,0,0]))) (TableTree.node 488 (TableTree.leaf (#[176,0,0,180,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[182,0,0,186,0,0,0,0,0,0,0,0])))) (TableTree.node 491 (TableTree.node 490 (TableTree.leaf (#[0,0,0,0,0,0,438,0,0,376,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,433,0,0,432,0,0]))) (TableTree.node 492 (TableTree.leaf (#[0,0,0,0,0,0,420,0,0,434,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,422,0,0,435,0,0]))))))) (TableTree.node 507 (TableTree.node 500 (TableTree.node 496 (TableTree.node 494 (TableTree.leaf (#[722,0,0,723,0,0,0,0,0,0,0,0])) (TableTree.node 495 (TableTree.leaf (#[724,0,0,716,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[717,0,0,718,0,0,0,0,0,0,0,0])))) (TableTree.node 498 (TableTree.node 497 (TableTree.leaf (#[719,0,0,720,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[187,641,0,0,0,0,903,0,0,0,0,0]))) (TableTree.node 499 (TableTree.leaf (#[770,0,0,0,0,0,885,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,742,0,0,875,0,0]))))) (TableTree.node 503 (TableTree.node 501 (TableTree.leaf (#[0,0,0,0,0,0,437,0,0,876,0,0])) (TableTree.node 502 (TableTree.leaf (#[721,0,0,0,0,0,885,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,437,0,0,876,0,0])))) (TableTree.node 505 (TableTree.node 504 (TableTree.leaf (#[0,0,0,0,0,0,417,0,0,830,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,385,0,0,826,0,0]))) (TableTree.node 506 (TableTree.leaf (#[0,0,0,0,0,0,772,0,0,771,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,420,0,0,419,0,0])))))) (TableTree.node 514 (TableTree.node 510 (TableTree.node 508 (TableTree.leaf (#[0,0,0,0,0,0,385,0,0,826,0,0])) (TableTree.node 509 (TableTree.leaf (#[0,0,0,0,0,0,420,0,0,419,0,0])) (TableTree.leaf (#[188,0,0,0,0,0,894,912,0,0,0,0])))) (TableTree.node 512 (TableTree.node 511 (TableTree.leaf (#[0,0,0,0,0,0,896,914,0,853,824,0])) (TableTree.leaf (#[0,0,0,0,0,0,898,916,0,854,832,0]))) (TableTree.node 513 (TableTree.leaf (#[0,0,0,0,0,0,900,918,0,857,838,0])) (TableTree.leaf (#[0,0,0,0,0,0,911,0,0,859,0,0]))))) (TableTree.node 518 (TableTree.node 516 (TableTree.node 515 (TableTree.leaf (#[0,0,0,0,0,0,893,0,0,864,0,0])) (TableTree.leaf (#[750,0,0,751,0,0,0,0,0,0,0,0]))) (TableTree.node 517 (TableTree.leaf (#[0,0,0,0,0,0,893,0,0,864,0,0])) (TableTree.leaf (#[773,0,0,774,0,0,0,0,0,0,0,0])))) (TableTree.node 520 (TableTree.node 519 (TableTree.leaf (#[775,0,0,763,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[166,0,0,776,0,0,0,0,0,0,0,0]))) (TableTree.node 521 (TableTree.leaf (#[777,0,0,718,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,902,920,0,842,845,0])))))))) (TableTree.node 551 (TableTree.node 536 (TableTree.node 529 (TableTree.node 525 (TableTree.node 523 (TableTree.leaf (#[721,0,0,0,0,0,885,0,0,0,0,0])) (TableTree.node 524 (TableTree.leaf (#[0,0,0,0,0,0,437,0,0,430,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,385,0,0,826,0,0])))) (TableTree.node 527 (TableTree.node 526 (TableTree.leaf (#[0,0,0,0,0,0,420,0,0,419,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,422,0,0,435,0,0]))) (TableTree.node 528 (TableTree.leaf (#[778,0,0,779,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[780,0,0,0,0,0,781,0,0,0,0,0]))))) (TableTree.node 532 (TableTree.node 530 (TableTree.leaf (#[0,0,0,0,0,0,887,0,0,849,0,0])) (TableTree.node 531 (TableTree.leaf (#[0,0,0,0,0,0,385,0,0,826,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,433,0,0,782,0,0])))) (TableTree.node 534 (TableTree.node 533 (TableTree.leaf (#[0,0,0,0,0,0,839,0,0,869,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,712,0,0,400,0,0]))) (TableTree.node 535 (TableTree.leaf (#[0,0,0,0,0,0,839,0,0,869,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,712,0,0,400,0,0])))))) (TableTree.node 543 (TableTree.node 539 (TableTree.node 537 (TableTree.leaf (#[861,0,0,430,0,0,0,0,0,0,0,0])) (TableTree.node 538 (TableTree.leaf (#[431,0,0,432,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[821,822,0,379,380,0,0,0,0,0,0,0])))) (TableTree.node 541 (TableTree.node 540 (TableTree.leaf (#[865,0,0,701,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[727,728,0,729,730,0,0,0,0,0,0,0]))) (TableTree.node 542 (TableTree.leaf (#[731,0,0,732,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[823,0,0,913,0,0,0,0,0,0,0,0]))))) (TableTree.node 547 (TableTree.node 545 (TableTree.node 544 (TableTree.leaf (#[831,0,0,915,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[178,0,0,183,0,0,0,0,0,0,0,0]))) (TableTree.node 546 (TableTree.leaf (#[783,0,0,0,0,0,402,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,438,0,0,376,0,0])))) (TableTree.node 549 (TableTree.node 548 (TableTree.leaf (#[0,0,0,0,0,0,433,0,0,432,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,420,0,0,434,0,0]))) (TableTree.node 550 (TableTree.leaf (#[0,0,0,0,0,0,422,0,0,435,0,0])) (TableTree.leaf (#[402,0,0,376,0,0,0,0,0,0,0,0]))))))) (TableTree.node 565 (TableTree.node 558 (TableTree.node 554 (TableTree.node 552 (TableTree.leaf (#[438,0,0,432,0,0,0,0,0,0,0,0])) (TableTree.node 553 (TableTree.leaf (#[870,0,0,890,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[839,0,0,400,0,0,0,0,0,0,0,0])))) (TableTree.node 556 (TableTree.node 555 (TableTree.leaf (#[401,0,0,0,0,0,402,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,438,0,0,735,0,0]))) (TableTree.node 557 (TableTree.leaf (#[833,834,0,835,908,0,0,0,0,0,0,0])) (TableTree.leaf (#[872,0,0,925,0,0,0,0,0,0,0,0]))))) (TableTree.node 561 (TableTree.node 559 (TableTree.leaf (#[858,856,0,738,739,0,0,0,0,0,0,0])) (TableTree.node 560 (TableTree.leaf (#[868,0,0,709,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[837,0,0,917,0,0,0,0,0,0,0,0])))) (TableTree.node 563 (TableTree.node 562 (TableTree.leaf (#[844,0,0,919,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[846,847,0,0,0,0,903,0,0,0,0,0]))) (TableTree.node 564 (TableTree.leaf (#[874,0,0,0,0,0,885,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,742,0,0,875,0,0])))))) (TableTree.node 572 (TableTree.node 568 (TableTree.node 566 (TableTree.leaf (#[0,0,0,0,0,0,437,0,0,876,0,0])) (TableTree.node 567 (TableTree.leaf (#[848,0,0,0,0,0,894,912,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,896,914,0,853,824,0])))) (TableTree.node 570 (TableTree.node 569 (TableTree.leaf (#[0,0,0,0,0,0,385,0,0,826,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,420,0,0,419,0,0]))) (TableTree.node 571 (TableTree.leaf (#[0,0,0,0,0,0,422,0,0,435,0,0])) (TableTree.leaf (#[402,0,0,376,0,0,0,0,0,0,0,0]))))) (TableTree.node 576 (TableTree.node 574 (TableTree.node 573 (TableTree.leaf (#[0,0,0,0,0,0,907,0,0,877,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,889,0,0,879,0,0]))) (TableTree.node 575 (TableTree.leaf (#[0,0,0,0,0,0,909,0,0,855,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,747,0,0,871,0,0])))) (TableTree.node 578 (TableTree.node 577 (TableTree.leaf (#[0,0,0,0,0,0,898,916,0,854,832,0])) (TableTree.leaf (#[0,0,0,0,0,0,900,918,0,857,838,0]))) (TableTree.node 579 (TableTree.leaf (#[0,0,0,0,0,0,911,0,0,859,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,893,0,0,864,0,0]))))))))) (TableTree.node 638 (TableTree.node 609 (TableTree.node 594 (TableTree.node 587 (TableTree.node 583 (TableTree.node 581 (TableTree.leaf (#[865,0,0,701,0,0,0,0,0,0,0,0])) (TableTree.node 582 (TableTree.leaf (#[0,0,0,0,0,0,902,920,0,842,845,0])) (TableTree.leaf (#[821,822,0,379,380,0,0,0,0,0,0,0])))) (TableTree.node 585 (TableTree.node 584 (TableTree.leaf (#[823,0,0,913,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[870,0,0,890,0,0,0,0,0,0,0,0]))) (TableTree.node 586 (TableTree.leaf (#[839,0,0,400,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[401,0,0,0,0,0,402,0,0,0,0,0]))))) (TableTree.node 590 (TableTree.node 588 (TableTree.leaf (#[0,0,0,0,0,0,438,0,0,735,0,0])) (TableTree.node 589 (TableTree.leaf (#[0,0,0,0,0,0,385,0,0,826,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,420,0,0,419,0,0])))) (TableTree.node 592 (TableTree.node 591 (TableTree.leaf (#[0,0,0,0,0,0,422,0,0,435,0,0])) (TableTree.leaf (#[825,0,0,826,0,0,0,0,0,0,0,0]))) (TableTree.node 593 (TableTree.leaf (#[385,0,0,386,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[839,0,0,400,0,0,0,0,0,0,0,0])))))) (TableTree.node 601 (TableTree.node 597 (TableTree.node 595 (TableTree.leaf (#[401,0,0,0,0,0,402,0,0,0,0,0])) (TableTree.node 596 (TableTree.leaf (#[866,0,0,923,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[706,0,0,707,0,0,0,0,0,0,0,0])))) (TableTree.node 599 (TableTree.node 598 (TableTree.leaf (#[827,828,0,829,906,0,0,0,0,0,0,0])) (TableTree.leaf (#[831,0,0,915,0,0,0,0,0,0,0,0]))) (TableTree.node 600 (TableTree.leaf (#[833,834,0,835,908,0,0,0,0,0,0,0])) (TableTree.leaf (#[837,0,0,917,0,0,0,0,0,0,0,0]))))) (TableTree.node 605 (TableTree.node 603 (TableTree.node 602 (TableTree.leaf (#[868,0,0,709,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[710,0,0,0,0,0,402,0,0,0,0,0]))) (TableTree.node 604 (TableTree.leaf (#[840,841,0,901,910,0,0,0,0,0,0,0])) (TableTree.leaf (#[844,0,0,919,0,0,0,0,0,0,0,0])))) (TableTree.node 607 (TableTree.node 606 (TableTree.leaf (#[846,847,0,0,0,0,903,0,0,0,0,0])) (TableTree.leaf (#[848,0,0,0,0,0,894,912,0,0,0,0]))) (TableTree.node 608 (TableTree.leaf (#[0,0,0,0,0,0,887,0,0,849,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,385,0,0,826,0,0]))))))) (TableTree.node 623 (TableTree.node 616 (TableTree.node 612 (TableTree.node 610 (TableTree.leaf (#[0,0,0,0,0,0,420,0,0,419,0,0])) (TableTree.node 611 (TableTree.leaf (#[0,0,0,0,0,0,422,0,0,421,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,887,0,0,849,0,0])))) (TableTree.node 614 (TableTree.node 613 (TableTree.leaf (#[0,0,0,0,0,0,385,0,0,826,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,905,0,0,851,0,0]))) (TableTree.node 615 (TableTree.leaf (#[0,0,0,0,0,0,896,914,0,853,824,0])) (TableTree.leaf (#[0,0,0,0,0,0,417,0,0,830,0,0]))))) (TableTree.node 619 (TableTree.node 617 (TableTree.leaf (#[0,0,0,0,0,0,898,916,0,854,832,0])) (TableTree.node 618 (TableTree.leaf (#[0,0,0,0,0,0,839,0,0,869,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,712,0,0,400,0,0])))) (TableTree.node 621 (TableTree.node 620 (TableTree.leaf (#[0,0,0,0,0,0,909,0,0,855,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,900,918,0,857,838,0]))) (TableTree.node 622 (TableTree.leaf (#[0,0,0,0,0,0,911,0,0,859,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,902,920,0,842,845,0])))))) (TableTree.node 630 (TableTree.node 626 (TableTree.node 624 (TableTree.leaf (#[438,0,0,432,0,0,0,0,0,0,0,0])) (TableTree.node 625 (TableTree.leaf (#[433,0,0,434,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[420,0,0,435,0,0,0,0,0,0,0,0])))) (TableTree.node 628 (TableTree.node 627 (TableTree.leaf (#[422,0,0,0,0,0,402,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,438,0,0,376,0,0]))) (TableTree.node 629 (TableTree.leaf (#[0,0,0,0,0,0,433,0,0,432,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,420,0,0,434,0,0]))))) (TableTree.node 634 (TableTree.node 632 (TableTree.node 631 (TableTree.leaf (#[0,0,0,0,0,0,422,0,0,435,0,0])) (TableTree.leaf (#[727,728,0,729,730,0,0,0,0,0,0,0]))) (TableTree.node 633 (TableTree.leaf (#[731,0,0,732,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[872,0,0,925,0,0,0,0,0,0,0,0])))) (TableTree.node 636 (TableTree.node 635 (TableTree.leaf (#[858,856,0,738,739,0,0,0,0,0,0,0])) (TableTree.leaf (#[874,0,0,0,0,0,885,0,0,0,0,0]))) (TableTree.node 637 (TableTree.leaf (#[0,0,0,0,0,0,742,0,0,875,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,437,0,0,876,0,0])))))))) (TableTree.node 667 (TableTree.node 652 (TableTree.node 645 (TableTree.node 641 (TableTree.node 639 (TableTree.leaf (#[0,0,0,0,0,0,907,0,0,877,0,0])) (TableTree.node 640 (TableTree.leaf (#[0,0,0,0,0,0,889,0,0,879,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,747,0,0,871,0,0])))) (TableTree.node 643 (TableTree.node 642 (TableTree.leaf (#[0,0,0,0,0,0,893,0,0,864,0,0])) (TableTree.leaf (#[821,822,0,379,380,0,0,0,0,0,0,0]))) (TableTree.node 644 (TableTree.leaf (#[865,0,0,701,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[727,728,0,729,730,0,0,0,0,0,0,0]))))) (TableTree.node 648 (TableTree.node 646 (TableTree.leaf (#[731,0,0,732,0,0,0,0,0,0,0,0])) (TableTree.node 647 (TableTree.leaf (#[861,0,0,430,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[431,0,0,432,0,0,0,0,0,0,0,0])))) (TableTree.node 650 (TableTree.node 649 (TableTree.leaf (#[784,785,0,786,787,0,0,0,0,0,0,0])) (TableTree.leaf (#[788,0,0,789,0,0,0,0,0,0,0,0]))) (TableTree.node 651 (TableTree.leaf (#[790,772,0,791,792,0,0,0,0,0,0,0])) (TableTree.leaf (#[793,0,0,794,0,0,0,0,0,0,0,0])))))) (TableTree.node 659 (TableTree.node 655 (TableTree.node 653 (TableTree.leaf (#[433,0,0,434,0,0,0,0,0,0,0,0])) (TableTree.node 654 (TableTree.leaf (#[420,0,0,435,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[823,0,0,913,0,0,0,0,0,0,0,0])))) (TableTree.node 657 (TableTree.node 656 (TableTree.leaf (#[831,0,0,915,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[837,0,0,917,0,0,0,0,0,0,0,0]))) (TableTree.node 658 (TableTree.leaf (#[844,0,0,919,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[846,847,0,0,0,0,903,0,0,0,0,0]))))) (TableTree.node 663 (TableTree.node 661 (TableTree.node 660 (TableTree.leaf (#[874,0,0,0,0,0,885,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,742,0,0,875,0,0]))) (TableTree.node 662 (TableTree.leaf (#[0,0,0,0,0,0,437,0,0,876,0,0])) (TableTree.leaf (#[862,0,0,0,0,0,885,0,0,0,0,0])))) (TableTree.node 665 (TableTree.node 664 (TableTree.leaf (#[0,0,0,0,0,0,437,0,0,876,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,417,0,0,830,0,0]))) (TableTree.node 666 (TableTree.leaf (#[0,0,0,0,0,0,385,0,0,826,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,772,0,0,771,0,0]))))))) (TableTree.node 681 (TableTree.node 674 (TableTree.node 670 (TableTree.node 668 (TableTree.leaf (#[0,0,0,0,0,0,420,0,0,419,0,0])) (TableTree.node 669 (TableTree.leaf (#[0,0,0,0,0,0,385,0,0,826,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,420,0,0,419,0,0])))) (TableTree.node 672 (TableTree.node 671 (TableTree.leaf (#[848,0,0,0,0,0,894,912,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,896,914,0,853,824,0]))) (TableTree.node 673 (TableTree.leaf (#[0,0,0,0,0,0,898,916,0,854,832,0])) (TableTree.leaf (#[0,0,0,0,0,0,900,918,0,857,838,0]))))) (TableTree.node 677 (TableTree.node 675 (TableTree.leaf (#[0,0,0,0,0,0,911,0,0,859,0,0])) (TableTree.node 676 (TableTree.leaf (#[0,0,0,0,0,0,893,0,0,864,0,0])) (TableTree.leaf (#[865,0,0,701,0,0,0,0,0,0,0,0])))) (TableTree.node 679 (TableTree.node 678 (TableTree.leaf (#[0,0,0,0,0,0,893,0,0,864,0,0])) (TableTree.leaf (#[881,0,0,796,0,0,0,0,0,0,0,0]))) (TableTree.node 680 (TableTree.leaf (#[797,0,0,789,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[850,0,0,798,0,0,0,0,0,0,0,0])))))) (TableTree.node 688 (TableTree.node 684 (TableTree.node 682 (TableTree.leaf (#[749,0,0,434,0,0,0,0,0,0,0,0])) (TableTree.node 683 (TableTree.leaf (#[0,0,0,0,0,0,902,920,0,842,845,0])) (TableTree.leaf (#[821,822,0,379,380,0,0,0,0,0,0,0])))) (TableTree.node 686 (TableTree.node 685 (TableTree.leaf (#[827,828,0,829,906,0,0,0,0,0,0,0])) (TableTree.leaf (#[833,834,0,835,908,0,0,0,0,0,0,0]))) (TableTree.node 687 (TableTree.leaf (#[882,0,0,927,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[884,0,0,0,0,0,781,0,0,0,0,0]))))) (TableTree.node 692 (TableTree.node 690 (TableTree.node 689 (TableTree.leaf (#[863,0,0,892,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,887,0,0,849,0,0]))) (TableTree.node 691 (TableTree.leaf (#[0,0,0,0,0,0,385,0,0,826,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,433,0,0,782,0,0])))) (TableTree.node 694 (TableTree.node 693 (TableTree.leaf (#[840,841,0,901,910,0,0,0,0,0,0,0])) (TableTree.leaf (#[846,847,0,0,0,0,903,0,0,0,0,0]))) (TableTree.node 695 (TableTree.leaf (#[0,0,0,0,0,0,905,0,0,851,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,417,0,0,830,0,0])))))))))) (TableTree.node 812 (TableTree.node 754 (TableTree.node 725 (TableTree.node 710 (TableTree.node 703 (TableTree.node 699 (TableTree.node 697 (TableTree.leaf (#[0,0,0,0,0,0,839,0,0,869,0,0])) (TableTree.node 698 (TableTree.leaf (#[0,0,0,0,0,0,712,0,0,400,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,839,0,0,869,0,0])))) (TableTree.node 701 (TableTree.node 700 (TableTree.leaf (#[0,0,0,0,0,0,712,0,0,400,0,0])) (TableTree.leaf (#[861,812,0,430,813,0,0,0,0,0,0,0]))) (TableTree.node 702 (TableTree.leaf (#[431,814,0,432,815,0,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,909,0,0,855,0,0]))))) (TableTree.node 706 (TableTree.node 704 (TableTree.leaf (#[0,0,0,0,0,0,911,0,0,859,0,0])) (TableTree.node 705 (TableTree.leaf (#[870,816,0,890,817,0,0,0,0,0,0,0])) (TableTree.leaf (#[839,818,0,400,819,0,0,0,0,0,0,0])))) (TableTree.node 708 (TableTree.node 707 (TableTree.leaf (#[401,820,0,0,0,0,402,812,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,438,814,0,735,813,0]))) (TableTree.node 709 (TableTree.leaf (#[0,0,0,0,0,0,385,816,0,826,815,0])) (TableTree.leaf (#[0,0,0,0,0,0,420,818,0,419,817,0])))))) (TableTree.node 717 (TableTree.node 713 (TableTree.node 711 (TableTree.leaf (#[0,0,0,0,0,0,422,820,0,435,819,0])) (TableTree.node 712 (TableTree.leaf (#[0,0,0,0,0,0,887,814,0,849,813,0])) (TableTree.leaf (#[0,0,0,0,0,0,422,820,0,421,819,0])))) (TableTree.node 715 (TableTree.node 714 (TableTree.leaf (#[861,0,0,430,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[431,0,0,432,0,0,0,0,0,0,0,0]))) (TableTree.node 716 (TableTree.leaf (#[433,0,0,434,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[420,0,0,435,0,0,0,0,0,0,0,0]))))) (TableTree.node 721 (TableTree.node 719 (TableTree.node 718 (TableTree.leaf (#[422,0,0,0,0,0,402,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,438,0,0,376,0,0]))) (TableTree.node 720 (TableTree.leaf (#[0,0,0,0,0,0,433,0,0,432,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,420,0,0,434,0,0])))) (TableTree.node 723 (TableTree.node 722 (TableTree.leaf (#[0,0,0,0,0,0,893,0,0,864,0,0])) (TableTree.leaf (#[402,0,0,376,0,0,0,0,0,0,0,0]))) (TableTree.node 724 (TableTree.leaf (#[438,0,0,432,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[433,0,0,434,0,0,0,0,0,0,0,0]))))))) (TableTree.node 739 (TableTree.node 732 (TableTree.node 728 (TableTree.node 726 (TableTree.leaf (#[0,0,0,0,0,0,889,0,0,879,0,0])) (TableTree.node 727 (TableTree.leaf (#[0,0,0,0,0,0,839,0,0,869,0,0])) (TableTree.leaf (#[784,785,816,786,787,817,0,0,0,0,0,0])))) (TableTree.node 730 (TableTree.node 729 (TableTree.leaf (#[788,816,0,789,817,0,0,0,0,0,0,0])) (TableTree.leaf (#[790,772,818,791,792,819,0,0,0,0,0,0]))) (TableTree.node 731 (TableTree.leaf (#[793,818,0,794,819,0,0,0,0,0,0,0])) (TableTree.leaf (#[433,816,0,434,817,0,0,0,0,0,0,0]))))) (TableTree.node 735 (TableTree.node 733 (TableTree.leaf (#[420,818,0,435,819,0,0,0,0,0,0,0])) (TableTree.node 734 (TableTree.leaf (#[862,820,0,0,0,0,885,812,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,437,814,0,430,813,0])))) (TableTree.node 737 (TableTree.node 736 (TableTree.leaf (#[438,814,0,432,815,0,0,0,0,0,0,0])) (TableTree.leaf (#[862,820,0,0,0,0,885,812,0,0,0,0]))) (TableTree.node 738 (TableTree.leaf (#[0,0,0,0,0,0,437,814,0,876,813,0])) (TableTree.leaf (#[0,0,0,0,0,0,772,818,0,771,817,0])))))) (TableTree.node 746 (TableTree.node 742 (TableTree.node 740 (TableTree.leaf (#[0,0,0,0,0,0,420,818,0,419,817,0])) (TableTree.node 741 (TableTree.leaf (#[0,0,0,0,0,0,893,820,0,864,819,0])) (TableTree.leaf (#[881,814,0,796,815,0,0,0,0,0,0,0])))) (TableTree.node 744 (TableTree.node 743 (TableTree.leaf (#[797,816,0,789,817,0,0,0,0,0,0,0])) (TableTree.leaf (#[850,814,0,798,815,0,0,0,0,0,0,0]))) (TableTree.node 745 (TableTree.leaf (#[882,818,0,927,819,0,0,0,0,0,0,0])) (TableTree.leaf (#[884,820,0,0,0,0,781,812,0,0,0,0]))))) (TableTree.node 750 (TableTree.node 748 (TableTree.node 747 (TableTree.leaf (#[863,818,0,892,819,0,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,433,816,0,782,815,0]))) (TableTree.node 749 (TableTree.leaf (#[0,0,0,0,0,0,712,820,0,400,819,0])) (TableTree.leaf (#[422,820,0,0,0,0,402,812,0,0,0,0])))) (TableTree.node 752 (TableTree.node 751 (TableTree.leaf (#[861,0,0,430,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[431,0,0,432,0,0,0,0,0,0,0,0]))) (TableTree.node 753 (TableTree.leaf (#[784,785,0,786,787,0,0,0,0,0,0,0])) (TableTree.leaf (#[788,0,0,789,0,0,0,0,0,0,0,0])))))))) (TableTree.node 783 (TableTree.node 768 (TableTree.node 761 (TableTree.node 757 (TableTree.node 755 (TableTree.leaf (#[790,772,0,791,792,0,0,0,0,0,0,0])) (TableTree.node 756 (TableTree.leaf (#[793,0,0,794,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[433,0,0,434,0,0,0,0,0,0,0,0])))) (TableTree.node 759 (TableTree.node 758 (TableTree.leaf (#[420,0,0,435,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[802,803,0,0,0,0,804,0,0,0,0,0]))) (TableTree.node 760 (TableTree.leaf (#[805,0,0,0,0,0,402,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,807,0,0,806,0,0]))))) (TableTree.node 764 (TableTree.node 762 (TableTree.leaf (#[0,0,0,0,0,0,438,0,0,376,0,0])) (TableTree.node 763 (TableTree.leaf (#[422,0,0,0,0,0,402,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,438,0,0,376,0,0])))) (TableTree.node 766 (TableTree.node 765 (TableTree.leaf (#[0,0,0,0,0,0,785,0,0,730,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,433,0,0,432,0,0]))) (TableTree.node 767 (TableTree.leaf (#[0,0,0,0,0,0,772,0,0,787,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,420,0,0,434,0,0])))))) (TableTree.node 775 (TableTree.node 771 (TableTree.node 769 (TableTree.leaf (#[0,0,0,0,0,0,433,0,0,432,0,0])) (TableTree.node 770 (TableTree.leaf (#[0,0,0,0,0,0,420,0,0,434,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,893,0,0,864,0,0])))) (TableTree.node 773 (TableTree.node 772 (TableTree.leaf (#[0,0,0,0,0,0,438,814,0,376,813,0])) (TableTree.leaf (#[0,0,0,0,0,0,433,816,0,432,815,0]))) (TableTree.node 774 (TableTree.leaf (#[385,0,0,386,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[808,0,0,435,0,0,0,0,0,0,0,0]))))) (TableTree.node 779 (TableTree.node 777 (TableTree.node 776 (TableTree.leaf (#[422,0,0,0,0,0,402,0,0,0,0,0])) (TableTree.leaf (#[808,0,0,435,0,0,0,0,0,0,0,0]))) (TableTree.node 778 (TableTree.leaf (#[422,0,0,0,0,0,402,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,889,0,0,879,0,0])))) (TableTree.node 781 (TableTree.node 780 (TableTree.leaf (#[0,0,0,0,0,0,839,0,0,869,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,712,0,0,400,0,0]))) (TableTree.node 782 (TableTree.leaf (#[375,812,0,376,813,0,0,0,0,0,0,0])) (TableTree.leaf (#[420,818,0,435,819,0,0,0,0,0,0,0]))))))) (TableTree.node 797 (TableTree.node 790 (TableTree.node 786 (TableTree.node 784 (TableTree.leaf (#[0,0,0,0,0,0,422,0,0,435,0,0])) (TableTree.node 785 (TableTree.leaf (#[802,803,820,0,0,0,804,812,0,0,0,0])) (TableTree.leaf (#[805,820,0,0,0,0,402,812,0,0,0,0])))) (TableTree.node 788 (TableTree.node 787 (TableTree.leaf (#[0,0,0,0,0,0,807,814,0,806,813,0])) (TableTree.leaf (#[0,0,0,0,0,0,438,814,0,376,813,0]))) (TableTree.node 789 (TableTree.leaf (#[422,820,0,0,0,0,402,812,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,438,814,0,376,813,0]))))) (TableTree.node 793 (TableTree.node 791 (TableTree.leaf (#[0,0,0,0,0,0,785,816,0,730,815,0])) (TableTree.node 792 (TableTree.leaf (#[0,0,0,0,0,0,772,818,0,787,817,0])) (TableTree.leaf (#[0,0,0,0,0,0,420,818,0,434,817,0])))) (TableTree.node 795 (TableTree.node 794 (TableTree.leaf (#[0,0,0,0,0,0,433,816,0,432,815,0])) (TableTree.leaf (#[0,0,0,0,0,0,420,818,0,434,817,0]))) (TableTree.node 796 (TableTree.leaf (#[385,816,0,386,817,0,0,0,0,0,0,0])) (TableTree.leaf (#[808,818,0,435,819,0,0,0,0,0,0,0])))))) (TableTree.node 804 (TableTree.node 800 (TableTree.node 798 (TableTree.leaf (#[422,820,0,0,0,0,402,812,0,0,0,0])) (TableTree.node 799 (TableTree.leaf (#[808,818,0,435,819,0,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,889,816,0,879,815,0])))) (TableTree.node 802 (TableTree.node 801 (TableTree.leaf (#[0,0,0,0,0,0,839,818,0,869,817,0])) (TableTree.leaf (#[0,0,0,0,0,0,712,820,0,400,819,0]))) (TableTree.node 803 (TableTree.leaf (#[0,0,0,0,0,0,803,820,0,792,819,0])) (TableTree.leaf (#[0,0,0,0,0,0,422,820,0,435,819,0]))))) (TableTree.node 808 (TableTree.node 806 (TableTree.node 805 (TableTree.leaf (#[809,812,0,810,813,0,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,422,820,0,435,819,0]))) (TableTree.node 807 (TableTree.leaf (#[811,814,0,732,815,0,0,0,0,0,0,0])) (TableTree.leaf (#[788,816,0,789,817,0,0,0,0,0,0,0])))) (TableTree.node 810 (TableTree.node 809 (TableTree.leaf (#[0,0,0,0,0,0,433,816,0,432,815,0])) (TableTree.leaf (#[402,812,0,376,813,0,0,0,0,0,0,0]))) (TableTree.node 811 (TableTree.leaf (#[438,814,0,432,815,0,0,0,0,0,0,0])) (TableTree.leaf (#[433,816,0,434,817,0,0,0,0,0,0,0]))))))))) (TableTree.node 870 (TableTree.node 841 (TableTree.node 826 (TableTree.node 819 (TableTree.node 815 (TableTree.node 813 (TableTree.leaf (#[812,0,0,813,0,0,0,0,0,0,0,0])) (TableTree.node 814 (TableTree.leaf (#[814,0,0,815,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[816,0,0,817,0,0,0,0,0,0,0,0])))) (TableTree.node 817 (TableTree.node 816 (TableTree.leaf (#[818,0,0,819,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[820,0,0,0,0,0,812,0,0,0,0,0]))) (TableTree.node 818 (TableTree.leaf (#[0,0,0,0,0,0,814,0,0,813,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,816,0,0,815,0,0]))))) (TableTree.node 822 (TableTree.node 820 (TableTree.leaf (#[0,0,0,0,0,0,818,0,0,817,0,0])) (TableTree.node 821 (TableTree.leaf (#[0,0,0,0,0,0,820,0,0,819,0,0])) (TableTree.leaf (#[821,822,812,379,380,813,0,0,0,0,0,0])))) (TableTree.node 824 (TableTree.node 823 (TableTree.leaf (#[865,812,0,701,813,0,0,0,0,0,0,0])) (TableTree.leaf (#[823,812,0,913,813,0,0,0,0,0,0,0]))) (TableTree.node 825 (TableTree.leaf (#[831,814,0,915,815,0,0,0,0,0,0,0])) (TableTree.leaf (#[870,816,0,890,817,0,0,0,0,0,0,0])))))) (TableTree.node 833 (TableTree.node 829 (TableTree.node 827 (TableTree.leaf (#[839,818,0,400,819,0,0,0,0,0,0,0])) (TableTree.node 828 (TableTree.leaf (#[833,834,816,835,908,817,0,0,0,0,0,0])) (TableTree.leaf (#[872,816,0,925,817,0,0,0,0,0,0,0])))) (TableTree.node 831 (TableTree.node 830 (TableTree.leaf (#[858,856,818,738,739,819,0,0,0,0,0,0])) (TableTree.leaf (#[868,818,0,709,819,0,0,0,0,0,0,0]))) (TableTree.node 832 (TableTree.leaf (#[837,816,0,917,817,0,0,0,0,0,0,0])) (TableTree.leaf (#[844,818,0,919,819,0,0,0,0,0,0,0]))))) (TableTree.node 837 (TableTree.node 835 (TableTree.node 834 (TableTree.leaf (#[846,847,820,0,0,0,903,812,0,0,0,0])) (TableTree.leaf (#[874,820,0,0,0,0,885,812,0,0,0,0]))) (TableTree.node 836 (TableTree.leaf (#[0,0,0,0,0,0,742,814,0,875,813,0])) (TableTree.leaf (#[0,0,0,0,0,0,437,814,0,876,813,0])))) (TableTree.node 839 (TableTree.node 838 (TableTree.leaf (#[848,820,0,0,0,0,894,912,812,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,896,914,814,853,824,813]))) (TableTree.node 840 (TableTree.leaf (#[0,0,0,0,0,0,385,816,0,826,815,0])) (TableTree.leaf (#[0,0,0,0,0,0,907,816,0,877,815,0]))))))) (TableTree.node 855 (TableTree.node 848 (TableTree.node 844 (TableTree.node 842 (TableTree.leaf (#[0,0,0,0,0,0,889,816,0,879,815,0])) (TableTree.node 843 (TableTree.leaf (#[0,0,0,0,0,0,909,818,0,855,817,0])) (TableTree.leaf (#[0,0,0,0,0,0,747,818,0,871,817,0])))) (TableTree.node 846 (TableTree.node 845 (TableTree.leaf (#[0,0,0,0,0,0,898,916,816,854,832,815])) (TableTree.leaf (#[0,0,0,0,0,0,900,918,818,857,838,817]))) (TableTree.node 847 (TableTree.leaf (#[0,0,0,0,0,0,911,820,0,859,819,0])) (TableTree.leaf (#[0,0,0,0,0,0,893,820,0,864,819,0]))))) (TableTree.node 851 (TableTree.node 849 (TableTree.leaf (#[0,0,0,0,0,0,902,920,820,842,845,819])) (TableTree.node 850 (TableTree.leaf (#[825,814,0,826,815,0,0,0,0,0,0,0])) (TableTree.leaf (#[385,816,0,386,817,0,0,0,0,0,0,0])))) (TableTree.node 853 (TableTree.node 852 (TableTree.leaf (#[866,814,0,923,815,0,0,0,0,0,0,0])) (TableTree.leaf (#[706,816,0,707,817,0,0,0,0,0,0,0]))) (TableTree.node 854 (TableTree.leaf (#[827,828,814,829,906,815,0,0,0,0,0,0])) (TableTree.leaf (#[840,841,818,901,910,819,0,0,0,0,0,0])))))) (TableTree.node 862 (TableTree.node 858 (TableTree.node 856 (TableTree.leaf (#[0,0,0,0,0,0,887,814,0,849,813,0])) (TableTree.node 857 (TableTree.leaf (#[0,0,0,0,0,0,385,816,0,826,815,0])) (TableTree.leaf (#[0,0,0,0,0,0,905,814,0,851,813,0])))) (TableTree.node 860 (TableTree.node 859 (TableTree.leaf (#[0,0,0,0,0,0,417,816,0,830,815,0])) (TableTree.leaf (#[0,0,0,0,0,0,839,818,0,869,817,0]))) (TableTree.node 861 (TableTree.leaf (#[0,0,0,0,0,0,712,820,0,400,819,0])) (TableTree.leaf (#[861,812,0,430,813,0,0,0,0,0,0,0]))))) (TableTree.node 866 (TableTree.node 864 (TableTree.node 863 (TableTree.leaf (#[0,0,0,0,0,0,893,820,0,864,819,0])) (TableTree.leaf (#[0,0,0,0,0,0,889,816,0,879,815,0]))) (TableTree.node 865 (TableTree.leaf (#[0,0,0,0,0,0,839,818,0,869,817,0])) (TableTree.leaf (#[861,812,0,430,813,0,0,0,0,0,0,0])))) (TableTree.node 868 (TableTree.node 867 (TableTree.leaf (#[870,816,0,890,817,0,0,0,0,0,0,0])) (TableTree.leaf (#[839,818,0,400,819,0,0,0,0,0,0,0]))) (TableTree.node 869 (TableTree.leaf (#[0,0,0,0,0,0,385,816,0,826,815,0])) (TableTree.leaf (#[0,0,0,0,0,0,887,814,0,849,813,0])))))))) (TableTree.node 899 (TableTree.node 884 (TableTree.node 877 (TableTree.node 873 (TableTree.node 871 (TableTree.leaf (#[862,820,0,0,0,0,885,812,0,0,0,0])) (TableTree.node 872 (TableTree.leaf (#[0,0,0,0,0,0,437,814,0,430,813,0])) (TableTree.leaf (#[862,820,0,0,0,0,885,812,0,0,0,0])))) (TableTree.node 875 (TableTree.node 874 (TableTree.leaf (#[0,0,0,0,0,0,437,814,0,876,813,0])) (TableTree.leaf (#[0,0,0,0,0,0,893,820,0,864,819,0]))) (TableTree.node 876 (TableTree.leaf (#[881,814,0,796,815,0,0,0,0,0,0,0])) (TableTree.leaf (#[850,814,0,798,815,0,0,0,0,0,0,0]))))) (TableTree.node 880 (TableTree.node 878 (TableTree.leaf (#[882,818,0,927,819,0,0,0,0,0,0,0])) (TableTree.node 879 (TableTree.leaf (#[884,820,0,0,0,0,781,812,0,0,0,0])) (TableTree.leaf (#[863,818,0,892,819,0,0,0,0,0,0,0])))) (TableTree.node 882 (TableTree.node 881 (TableTree.leaf (#[0,0,0,0,0,0,712,820,0,400,819,0])) (TableTree.leaf (#[385,816,0,386,817,0,0,0,0,0,0,0]))) (TableTree.node 883 (TableTree.leaf (#[0,0,0,0,0,0,889,816,0,879,815,0])) (TableTree.leaf (#[0,0,0,0,0,0,839,818,0,869,817,0])))))) (TableTree.node 891 (TableTree.node 887 (TableTree.node 885 (TableTree.leaf (#[0,0,0,0,0,0,712,820,0,400,819,0])) (TableTree.node 886 (TableTree.leaf (#[885,812,0,430,813,0,0,0,0,0,0,0])) (TableTree.leaf (#[887,814,0,826,815,0,0,0,0,0,0,0])))) (TableTree.node 889 (TableTree.node 888 (TableTree.leaf (#[889,816,0,890,817,0,0,0,0,0,0,0])) (TableTree.leaf (#[891,818,0,892,819,0,0,0,0,0,0,0]))) (TableTree.node 890 (TableTree.leaf (#[893,820,0,0,0,0,885,812,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,887,814,0,886,813,0]))))) (TableTree.node 895 (TableTree.node 893 (TableTree.node 892 (TableTree.leaf (#[0,0,0,0,0,0,889,816,0,888,815,0])) (TableTree.leaf (#[0,0,0,0,0,0,839,818,0,890,817,0]))) (TableTree.node 894 (TableTree.leaf (#[0,0,0,0,0,0,893,820,0,892,819,0])) (TableTree.leaf (#[821,903,812,379,380,813,0,0,0,0,0,0])))) (TableTree.node 897 (TableTree.node 896 (TableTree.leaf (#[896,905,814,829,906,815,0,0,0,0,0,0])) (TableTree.leaf (#[898,907,816,835,908,817,0,0,0,0,0,0]))) (TableTree.node 898 (TableTree.leaf (#[900,909,818,901,910,819,0,0,0,0,0,0])) (TableTree.leaf (#[902,911,820,0,0,0,903,812,0,0,0,0]))))))) (TableTree.node 914 (TableTree.node 906 (TableTree.node 902 (TableTree.node 900 (TableTree.leaf (#[0,0,0,0,0,0,905,814,0,904,813,0])) (TableTree.node 901 (TableTree.leaf (#[0,0,0,0,0,0,907,816,0,906,815,0])) (TableTree.leaf (#[0,0,0,0,0,0,909,818,0,908,817,0])))) (TableTree.node 904 (TableTree.node 903 (TableTree.leaf (#[0,0,0,0,0,0,911,820,0,910,819,0])) (TableTree.leaf (#[921,812,0,701,813,0,0,0,0,0,0,0]))) (TableTree.node 905 (TableTree.leaf (#[922,814,0,923,815,0,0,0,0,0,0,0])) (TableTree.leaf (#[924,816,0,925,817,0,0,0,0,0,0,0]))))) (TableTree.node 910 (TableTree.node 908 (TableTree.node 907 (TableTree.leaf (#[926,818,0,927,819,0,0,0,0,0,0,0])) (TableTree.leaf (#[928,820,0,0,0,0,885,812,0,0,0,0]))) (TableTree.node 909 (TableTree.leaf (#[0,0,0,0,0,0,887,814,0,886,813,0])) (TableTree.leaf (#[0,0,0,0,0,0,889,816,0,888,815,0])))) (TableTree.node 912 (TableTree.node 911 (TableTree.leaf (#[0,0,0,0,0,0,839,818,0,890,817,0])) (TableTree.leaf (#[0,0,0,0,0,0,893,820,0,892,819,0]))) (TableTree.node 913 (TableTree.leaf (#[912,812,0,913,813,0,0,0,0,0,0,0])) (TableTree.leaf (#[914,814,0,915,815,0,0,0,0,0,0,0])))))) (TableTree.node 921 (TableTree.node 917 (TableTree.node 915 (TableTree.leaf (#[916,816,0,917,817,0,0,0,0,0,0,0])) (TableTree.node 916 (TableTree.leaf (#[918,818,0,919,819,0,0,0,0,0,0,0])) (TableTree.leaf (#[920,820,0,0,0,0,894,912,812,0,0,0])))) (TableTree.node 919 (TableTree.node 918 (TableTree.leaf (#[0,0,0,0,0,0,896,914,814,895,913,813])) (TableTree.leaf (#[0,0,0,0,0,0,898,916,816,897,915,815]))) (TableTree.node 920 (TableTree.leaf (#[0,0,0,0,0,0,900,918,818,899,917,817])) (TableTree.leaf (#[0,0,0,0,0,0,902,920,820,901,919,819]))))) (TableTree.node 925 (TableTree.node 923 (TableTree.node 922 (TableTree.leaf (#[861,812,0,430,813,0,0,0,0,0,0,0])) (TableTree.leaf (#[889,816,0,890,817,0,0,0,0,0,0,0]))) (TableTree.node 924 (TableTree.leaf (#[839,818,0,400,819,0,0,0,0,0,0,0])) (TableTree.leaf (#[893,820,0,0,0,0,885,812,0,0,0,0])))) (TableTree.node 927 (TableTree.node 926 (TableTree.leaf (#[0,0,0,0,0,0,437,814,0,876,813,0])) (TableTree.leaf (#[0,0,0,0,0,0,889,816,0,888,815,0]))) (TableTree.node 928 (TableTree.leaf (#[0,0,0,0,0,0,839,818,0,890,817,0])) (TableTree.leaf (#[0,0,0,0,0,0,893,820,0,892,819,0]))))))))))))
private def destAt (i : ℕ) : (Array ℕ) := if i < 929 then TableTree.lookup destAtTree i else #[]
private def parentAtTree : TableTree ((Array ℕ)) := (TableTree.node 464 (TableTree.node 232 (TableTree.node 116 (TableTree.node 58 (TableTree.node 29 (TableTree.node 14 (TableTree.node 7 (TableTree.node 3 (TableTree.node 1 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.node 2 (TableTree.leaf (#[1,1,1,0,0,0,0,0,0,1,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[2,2,2,0,0,0,0,0,0,2,2,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])))) (TableTree.node 5 (TableTree.node 4 (TableTree.leaf (#[3,3,3,0,0,0,0,0,0,3,3,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[5,5,5,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,5,5,5,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))) (TableTree.node 6 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,7,7,7,0,0,0,0,0,0,7,7,7,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,8,8,8,0,0,0,0,0,0,8,8,8,0,0,0,0,0,0]))))) (TableTree.node 10 (TableTree.node 8 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,10,10,10,0,0,0,0,0,0,10,10,10,0,0,0,0,0,0])) (TableTree.node 9 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,13,13,13,0,0,0,0,0,0,13,13,13,0,0,0,0,0,0])) (TableTree.leaf (#[15,15,15,0,0,0,0,0,0,15,15,15,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])))) (TableTree.node 12 (TableTree.node 11 (TableTree.leaf (#[18,18,18,0,0,0,0,0,0,18,18,18,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[20,20,20,0,0,0,0,0,0,20,20,20,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))) (TableTree.node 13 (TableTree.leaf (#[21,21,21,0,0,0,0,0,0,21,21,21,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[23,23,23,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,23,23,23,23,23,23,0,0,0,0,0,0,0,0,0,0,0,0])))))) (TableTree.node 21 (TableTree.node 17 (TableTree.node 15 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,27,27,27,27,27,27,0,0,0,27,27,27,27,27,27,0,0,0])) (TableTree.node 16 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,29,29,29,29,29,29,0,0,0,29,29,29,29,29,29,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,20,20,20,20,20,20,0,0,0,20,20,20,20,20,20,0,0,0])))) (TableTree.node 19 (TableTree.node 18 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,35,35,35,35,35,35,0,0,0,35,35,35,35,35,35,0,0,0])) (TableTree.leaf (#[39,39,39,0,0,0,0,0,0,39,39,39,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))) (TableTree.node 20 (TableTree.leaf (#[20,20,20,0,0,0,0,0,0,20,20,20,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[35,35,35,0,0,0,0,0,0,35,35,35,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))))) (TableTree.node 25 (TableTree.node 23 (TableTree.node 22 (TableTree.leaf (#[35,35,35,0,0,0,0,0,0,35,35,35,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0]))) (TableTree.node 24 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0])))) (TableTree.node 27 (TableTree.node 26 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0]))) (TableTree.node 28 (TableTree.leaf (#[47,47,47,0,0,0,0,0,0,47,47,47,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[46,46,46,0,0,0,0,0,0,46,46,46,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))))))) (TableTree.node 43 (TableTree.node 36 (TableTree.node 32 (TableTree.node 30 (TableTree.leaf (#[54,54,54,0,0,0,0,0,0,54,54,54,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.node 31 (TableTree.leaf (#[54,54,54,0,0,0,0,0,0,54,54,54,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[35,35,35,0,0,0,0,0,0,35,35,35,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])))) (TableTree.node 34 (TableTree.node 33 (TableTree.leaf (#[34,34,34,0,0,0,0,0,0,34,34,34,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[58,58,58,0,0,0,0,0,0,58,58,58,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))) (TableTree.node 35 (TableTree.leaf (#[58,58,58,0,0,0,0,0,0,58,58,58,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[60,60,60,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,60,60,60,60,60,60,0,0,0,0,0,0,0,0,0,0,0,0]))))) (TableTree.node 39 (TableTree.node 37 (TableTree.leaf (#[59,59,59,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,59,59,59,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.node 38 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0])))) (TableTree.node 41 (TableTree.node 40 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0]))) (TableTree.node 42 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,20,20,20,20,20,20,0,0,0,20,20,20,20,20,20,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,20,20,20,0,0,0,0,0,0,20,20,20,0,0,0,0,0,0])))))) (TableTree.node 50 (TableTree.node 46 (TableTree.node 44 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0])) (TableTree.node 45 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0])) (TableTree.leaf (#[69,69,69,0,0,0,0,0,0,69,69,69,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])))) (TableTree.node 48 (TableTree.node 47 (TableTree.leaf (#[21,21,21,0,0,0,0,0,0,21,21,21,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))) (TableTree.node 49 (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[20,20,20,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,20,20,20,20,20,20,0,0,0,0,0,0,0,0,0,0,0,0]))))) (TableTree.node 54 (TableTree.node 52 (TableTree.node 51 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,20,20,20,20,20,20,0,0,0,20,20,20,20,20,20,0,0,0]))) (TableTree.node 53 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0])))) (TableTree.node 56 (TableTree.node 55 (TableTree.leaf (#[42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))) (TableTree.node 57 (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])))))))) (TableTree.node 87 (TableTree.node 72 (TableTree.node 65 (TableTree.node 61 (TableTree.node 59 (TableTree.leaf (#[42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.node 60 (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])))) (TableTree.node 63 (TableTree.node 62 (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[42,42,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))) (TableTree.node 64 (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0]))))) (TableTree.node 68 (TableTree.node 66 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0])) (TableTree.node 67 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0])))) (TableTree.node 70 (TableTree.node 69 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0]))) (TableTree.node 71 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0])))))) (TableTree.node 79 (TableTree.node 75 (TableTree.node 73 (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.node 74 (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])))) (TableTree.node 77 (TableTree.node 76 (TableTree.leaf (#[43,43,43,0,0,0,0,0,0,43,43,43,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[20,20,20,0,0,0,0,0,0,20,20,20,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))) (TableTree.node 78 (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[20,20,20,0,0,0,0,0,0,20,20,20,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))))) (TableTree.node 83 (TableTree.node 81 (TableTree.node 80 (TableTree.leaf (#[42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[20,20,20,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,20,20,20,20,20,20,0,0,0,0,0,0,0,0,0,0,0,0]))) (TableTree.node 82 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0])) (TableTree.leaf (#[38,38,38,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,38,38,38,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])))) (TableTree.node 85 (TableTree.node 84 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,43,43,43,0,0,0,0,0,0,43,43,43,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0]))) (TableTree.node 86 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0]))))))) (TableTree.node 101 (TableTree.node 94 (TableTree.node 90 (TableTree.node 88 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0])) (TableTree.node 89 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0])) (TableTree.leaf (#[42,42,42,42,42,42,0,0,0,42,42,42,42,42,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])))) (TableTree.node 92 (TableTree.node 91 (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0]))) (TableTree.node 93 (TableTree.leaf (#[43,43,43,0,0,0,0,0,0,43,43,43,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))))) (TableTree.node 97 (TableTree.node 95 (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.node 96 (TableTree.leaf (#[44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])))) (TableTree.node 99 (TableTree.node 98 (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))) (TableTree.node 100 (TableTree.leaf (#[44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])))))) (TableTree.node 108 (TableTree.node 104 (TableTree.node 102 (TableTree.leaf (#[44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.node 103 (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])))) (TableTree.node 106 (TableTree.node 105 (TableTree.leaf (#[43,43,43,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,43,43,43,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0]))) (TableTree.node 107 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0]))))) (TableTree.node 112 (TableTree.node 110 (TableTree.node 109 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0]))) (TableTree.node 111 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0])))) (TableTree.node 114 (TableTree.node 113 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0]))) (TableTree.node 115 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,43,43,43,0,0,0,0,0,0,43,43,43,0,0,0,0,0,0]))))))))) (TableTree.node 174 (TableTree.node 145 (TableTree.node 130 (TableTree.node 123 (TableTree.node 119 (TableTree.node 117 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,43,43,43,0,0,0,0,0,0,43,43,43,0,0,0,0,0,0])) (TableTree.node 118 (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])))) (TableTree.node 121 (TableTree.node 120 (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))) (TableTree.node 122 (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0]))))) (TableTree.node 126 (TableTree.node 124 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0])) (TableTree.node 125 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0])))) (TableTree.node 128 (TableTree.node 127 (TableTree.leaf (#[42,42,42,42,42,42,0,0,0,42,42,42,42,42,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))) (TableTree.node 129 (TableTree.leaf (#[44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])))))) (TableTree.node 137 (TableTree.node 133 (TableTree.node 131 (TableTree.leaf (#[44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.node 132 (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])))) (TableTree.node 135 (TableTree.node 134 (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))) (TableTree.node 136 (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0]))))) (TableTree.node 141 (TableTree.node 139 (TableTree.node 138 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0]))) (TableTree.node 140 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0])))) (TableTree.node 143 (TableTree.node 142 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0]))) (TableTree.node 144 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0])) (TableTree.leaf (#[42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))))))) (TableTree.node 159 (TableTree.node 152 (TableTree.node 148 (TableTree.node 146 (TableTree.leaf (#[43,43,43,0,0,0,0,0,0,43,43,43,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.node 147 (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])))) (TableTree.node 150 (TableTree.node 149 (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))) (TableTree.node 151 (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))))) (TableTree.node 155 (TableTree.node 153 (TableTree.leaf (#[43,43,43,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,43,43,43,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.node 154 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,43,43,43,0,0,0,0,0,0,43,43,43,0,0,0,0,0,0])) (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0])))) (TableTree.node 157 (TableTree.node 156 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0]))) (TableTree.node 158 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0])))))) (TableTree.node 166 (TableTree.node 162 (TableTree.node 160 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0])) (TableTree.node 161 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0])) (TableTree.leaf (#[43,43,43,0,0,0,0,0,0,43,43,43,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])))) (TableTree.node 164 (TableTree.node 163 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0])) (TableTree.leaf (#[42,42,42,42,42,42,0,0,0,42,42,42,42,42,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))) (TableTree.node 165 (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))))) (TableTree.node 170 (TableTree.node 168 (TableTree.node 167 (TableTree.leaf (#[42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))) (TableTree.node 169 (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])))) (TableTree.node 172 (TableTree.node 171 (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))) (TableTree.node 173 (TableTree.leaf (#[43,43,43,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,43,43,43,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])))))))) (TableTree.node 203 (TableTree.node 188 (TableTree.node 181 (TableTree.node 177 (TableTree.node 175 (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.node 176 (TableTree.leaf (#[44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0])))) (TableTree.node 179 (TableTree.node 178 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0]))) (TableTree.node 180 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0]))))) (TableTree.node 184 (TableTree.node 182 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0])) (TableTree.node 183 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,43,43,43,0,0,0,0,0,0,43,43,43,0,0,0,0,0,0])))) (TableTree.node 186 (TableTree.node 185 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,43,43,43,0,0,0,0,0,0,43,43,43,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0]))) (TableTree.node 187 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0])))))) (TableTree.node 195 (TableTree.node 191 (TableTree.node 189 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0])) (TableTree.node 190 (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])))) (TableTree.node 193 (TableTree.node 192 (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))) (TableTree.node 194 (TableTree.leaf (#[42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[43,43,43,0,0,0,0,0,0,43,43,43,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))))) (TableTree.node 199 (TableTree.node 197 (TableTree.node 196 (TableTree.leaf (#[68,68,68,0,0,0,0,0,0,68,68,68,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[41,41,41,0,0,0,0,0,0,41,41,41,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))) (TableTree.node 198 (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0])))) (TableTree.node 201 (TableTree.node 200 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0]))) (TableTree.node 202 (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0]))))))) (TableTree.node 217 (TableTree.node 210 (TableTree.node 206 (TableTree.node 204 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0])) (TableTree.node 205 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,43,43,43,0,0,0,0,0,0,43,43,43,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0])))) (TableTree.node 208 (TableTree.node 207 (TableTree.leaf (#[42,42,42,42,42,42,0,0,0,42,42,42,42,42,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))) (TableTree.node 209 (TableTree.leaf (#[44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))))) (TableTree.node 213 (TableTree.node 211 (TableTree.leaf (#[44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.node 212 (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,68,68,68,0,0,0,0,0,0,68,68,68,0,0,0,0,0,0])))) (TableTree.node 215 (TableTree.node 214 (TableTree.leaf (#[41,41,41,0,0,0,0,0,0,41,41,41,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[68,68,68,0,0,0,0,0,0,68,68,68,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))) (TableTree.node 216 (TableTree.leaf (#[41,41,41,0,0,0,0,0,0,41,41,41,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])))))) (TableTree.node 224 (TableTree.node 220 (TableTree.node 218 (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.node 219 (TableTree.leaf (#[44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0])))) (TableTree.node 222 (TableTree.node 221 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0]))) (TableTree.node 223 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0]))))) (TableTree.node 228 (TableTree.node 226 (TableTree.node 225 (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))) (TableTree.node 227 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0])))) (TableTree.node 230 (TableTree.node 229 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0]))) (TableTree.node 231 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0])))))))))) (TableTree.node 348 (TableTree.node 290 (TableTree.node 261 (TableTree.node 246 (TableTree.node 239 (TableTree.node 235 (TableTree.node 233 (TableTree.leaf (#[42,42,42,42,42,42,0,0,0,42,42,42,42,42,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.node 234 (TableTree.leaf (#[42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[43,43,43,43,43,43,0,0,0,43,43,43,43,43,43,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])))) (TableTree.node 237 (TableTree.node 236 (TableTree.leaf (#[43,43,43,0,0,0,0,0,0,43,43,43,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))) (TableTree.node 238 (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,43,43,43,0,0,0,0,0,0,43,43,43,0,0,0,0,0,0]))))) (TableTree.node 242 (TableTree.node 240 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,43,43,43,0,0,0,0,0,0,43,43,43,0,0,0,0,0,0])) (TableTree.node 241 (TableTree.leaf (#[68,68,68,0,0,0,0,0,0,68,68,68,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[41,41,41,0,0,0,0,0,0,41,41,41,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])))) (TableTree.node 244 (TableTree.node 243 (TableTree.leaf (#[44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))) (TableTree.node 245 (TableTree.leaf (#[42,42,42,42,42,42,0,0,0,42,42,42,42,42,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])))))) (TableTree.node 253 (TableTree.node 249 (TableTree.node 247 (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.node 248 (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])))) (TableTree.node 251 (TableTree.node 250 (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0]))) (TableTree.node 252 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0])) (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0]))))) (TableTree.node 257 (TableTree.node 255 (TableTree.node 254 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0])) (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))) (TableTree.node 256 (TableTree.leaf (#[42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[43,43,43,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,43,43,43,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])))) (TableTree.node 259 (TableTree.node 258 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,43,43,43,0,0,0,0,0,0,43,43,43,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0]))) (TableTree.node 260 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0]))))))) (TableTree.node 275 (TableTree.node 268 (TableTree.node 264 (TableTree.node 262 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0])) (TableTree.node 263 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0])))) (TableTree.node 266 (TableTree.node 265 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0]))) (TableTree.node 267 (TableTree.leaf (#[42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0]))))) (TableTree.node 271 (TableTree.node 269 (TableTree.leaf (#[42,42,42,42,42,42,0,0,0,42,42,42,42,42,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.node 270 (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0])))) (TableTree.node 273 (TableTree.node 272 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,43,43,43,0,0,0,0,0,0,43,43,43,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,68,68,68,0,0,0,0,0,0,68,68,68,0,0,0,0,0,0]))) (TableTree.node 274 (TableTree.leaf (#[41,41,41,0,0,0,0,0,0,41,41,41,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])))))) (TableTree.node 282 (TableTree.node 278 (TableTree.node 276 (TableTree.leaf (#[42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.node 277 (TableTree.leaf (#[44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])))) (TableTree.node 280 (TableTree.node 279 (TableTree.leaf (#[44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))) (TableTree.node 281 (TableTree.leaf (#[42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[43,43,43,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,43,43,43,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))))) (TableTree.node 286 (TableTree.node 284 (TableTree.node 283 (TableTree.leaf (#[44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))) (TableTree.node 285 (TableTree.leaf (#[44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0])))) (TableTree.node 288 (TableTree.node 287 (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))) (TableTree.node 289 (TableTree.leaf (#[42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[43,43,43,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,43,43,43,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])))))))) (TableTree.node 319 (TableTree.node 304 (TableTree.node 297 (TableTree.node 293 (TableTree.node 291 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0])) (TableTree.node 292 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0])))) (TableTree.node 295 (TableTree.node 294 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0]))) (TableTree.node 296 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0]))))) (TableTree.node 300 (TableTree.node 298 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0])) (TableTree.node 299 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0])))) (TableTree.node 302 (TableTree.node 301 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0]))) (TableTree.node 303 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,68,68,68,0,0,0,0,0,0,68,68,68,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,41,41,41,0,0,0,0,0,0,41,41,41,0,0,0,0,0,0])))))) (TableTree.node 311 (TableTree.node 307 (TableTree.node 305 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,68,68,68,0,0,0,0,0,0,68,68,68,0,0,0,0,0,0])) (TableTree.node 306 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,41,41,41,0,0,0,0,0,0,41,41,41,0,0,0,0,0,0])) (TableTree.leaf (#[42,42,42,42,42,42,0,0,0,42,42,42,42,42,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])))) (TableTree.node 309 (TableTree.node 308 (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))) (TableTree.node 310 (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))))) (TableTree.node 315 (TableTree.node 313 (TableTree.node 312 (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))) (TableTree.node 314 (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])))) (TableTree.node 317 (TableTree.node 316 (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0]))) (TableTree.node 318 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0]))))))) (TableTree.node 333 (TableTree.node 326 (TableTree.node 322 (TableTree.node 320 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0])) (TableTree.node 321 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0])))) (TableTree.node 324 (TableTree.node 323 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0]))) (TableTree.node 325 (TableTree.leaf (#[42,42,42,42,42,42,0,0,0,42,42,42,42,42,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))))) (TableTree.node 329 (TableTree.node 327 (TableTree.leaf (#[43,43,43,43,43,43,0,0,0,43,43,43,43,43,43,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.node 328 (TableTree.leaf (#[43,43,43,0,0,0,0,0,0,43,43,43,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])))) (TableTree.node 331 (TableTree.node 330 (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))) (TableTree.node 332 (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[42,42,42,42,42,42,0,0,0,42,42,42,42,42,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])))))) (TableTree.node 340 (TableTree.node 336 (TableTree.node 334 (TableTree.leaf (#[42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.node 335 (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])))) (TableTree.node 338 (TableTree.node 337 (TableTree.leaf (#[44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))) (TableTree.node 339 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0]))))) (TableTree.node 344 (TableTree.node 342 (TableTree.node 341 (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0]))) (TableTree.node 343 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0])))) (TableTree.node 346 (TableTree.node 345 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0]))) (TableTree.node 347 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0]))))))))) (TableTree.node 406 (TableTree.node 377 (TableTree.node 362 (TableTree.node 355 (TableTree.node 351 (TableTree.node 349 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0])) (TableTree.node 350 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0])) (TableTree.leaf (#[42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])))) (TableTree.node 353 (TableTree.node 352 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0])) (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))) (TableTree.node 354 (TableTree.leaf (#[42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))))) (TableTree.node 358 (TableTree.node 356 (TableTree.leaf (#[43,43,43,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,43,43,43,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.node 357 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0])))) (TableTree.node 360 (TableTree.node 359 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0]))) (TableTree.node 361 (TableTree.leaf (#[42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[43,43,43,0,0,0,0,0,0,43,43,43,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])))))) (TableTree.node 369 (TableTree.node 365 (TableTree.node 363 (TableTree.leaf (#[68,68,68,0,0,0,0,0,0,68,68,68,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.node 364 (TableTree.leaf (#[41,41,41,0,0,0,0,0,0,41,41,41,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])))) (TableTree.node 367 (TableTree.node 366 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0]))) (TableTree.node 368 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,43,43,43,0,0,0,0,0,0,43,43,43,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,68,68,68,0,0,0,0,0,0,68,68,68,0,0,0,0,0,0]))))) (TableTree.node 373 (TableTree.node 371 (TableTree.node 370 (TableTree.leaf (#[41,41,41,0,0,0,0,0,0,41,41,41,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[68,68,68,0,0,0,0,0,0,68,68,68,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))) (TableTree.node 372 (TableTree.leaf (#[41,41,41,0,0,0,0,0,0,41,41,41,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])))) (TableTree.node 375 (TableTree.node 374 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,43,43,43,0,0,0,0,0,0,43,43,43,0,0,0,0,0,0]))) (TableTree.node 376 (TableTree.leaf (#[68,68,68,68,68,68,0,0,0,68,68,68,68,68,68,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[41,41,41,41,41,41,0,0,0,41,41,41,41,41,41,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))))))) (TableTree.node 391 (TableTree.node 384 (TableTree.node 380 (TableTree.node 378 (TableTree.leaf (#[42,42,42,42,42,42,42,42,42,42,42,42,42,42,42,42,42,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.node 379 (TableTree.leaf (#[42,42,42,42,42,42,0,0,0,42,42,42,42,42,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[43,43,43,43,43,43,43,43,43,43,43,43,43,43,43,43,43,43,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])))) (TableTree.node 382 (TableTree.node 381 (TableTree.leaf (#[43,43,43,43,43,43,0,0,0,43,43,43,43,43,43,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))) (TableTree.node 383 (TableTree.leaf (#[44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))))) (TableTree.node 387 (TableTree.node 385 (TableTree.leaf (#[42,42,42,42,42,42,0,0,0,42,42,42,42,42,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.node 386 (TableTree.leaf (#[43,43,43,43,43,43,0,0,0,0,0,0,0,0,0,0,0,0,43,43,43,43,43,43,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,43,43,43,43,43,43,0,0,0,43,43,43,43,43,43,0,0,0])))) (TableTree.node 389 (TableTree.node 388 (TableTree.leaf (#[44,44,44,44,44,44,44,44,44,44,44,44,44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))) (TableTree.node 390 (TableTree.leaf (#[42,42,42,42,42,42,42,42,42,42,42,42,42,42,42,42,42,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[42,42,42,42,42,42,0,0,0,42,42,42,42,42,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])))))) (TableTree.node 398 (TableTree.node 394 (TableTree.node 392 (TableTree.leaf (#[44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.node 393 (TableTree.leaf (#[44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[44,44,44,44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0])))) (TableTree.node 396 (TableTree.node 395 (TableTree.leaf (#[44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,42,42,42,42,42,0,0,0,42,42,42,42,42,42,0,0,0]))) (TableTree.node 397 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,42,42,42,42,42,0,0,0,42,42,42,42,42,42,0,0,0])) (TableTree.leaf (#[44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,44,44,44,0,0,0,0,0,0,0,0,0]))))) (TableTree.node 402 (TableTree.node 400 (TableTree.node 399 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,44,44,44,44,44,44,44,44,44,44,44,44])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,42,42,42,42,42,0,0,0,42,42,42,42,42,42,0,0,0]))) (TableTree.node 401 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,43,43,43,43,43,43,0,0,0,43,43,43,43,43,43,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,68,68,68,68,68,68,0,0,0,68,68,68,68,68,68,0,0,0])))) (TableTree.node 404 (TableTree.node 403 (TableTree.leaf (#[41,41,41,41,41,41,0,0,0,41,41,41,41,41,41,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0]))) (TableTree.node 405 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0])))))))) (TableTree.node 435 (TableTree.node 420 (TableTree.node 413 (TableTree.node 409 (TableTree.node 407 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,42,42,42,42,42,0,0,0,42,42,42,42,42,42,0,0,0])) (TableTree.node 408 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,44,44,44,44,44,44,44,44,44,44,44,44])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,44,44,44,44,44,44,44,44,44,44,44,44])))) (TableTree.node 411 (TableTree.node 410 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0]))) (TableTree.node 412 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,44,44,44,44,44,44,44,44,44,44,44,44])) (TableTree.leaf (#[44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))))) (TableTree.node 416 (TableTree.node 414 (TableTree.leaf (#[42,42,42,42,42,42,0,0,0,42,42,42,42,42,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.node 415 (TableTree.leaf (#[44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[42,42,42,42,42,42,0,0,0,42,42,42,42,42,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])))) (TableTree.node 418 (TableTree.node 417 (TableTree.leaf (#[44,44,44,44,44,44,44,44,44,44,44,44,44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[43,43,43,43,43,43,0,0,0,0,0,0,0,0,0,0,0,0,43,43,43,43,43,43,0,0,0,0,0,0,0,0,0,0,0,0]))) (TableTree.node 419 (TableTree.leaf (#[44,44,44,44,44,44,44,44,44,44,44,44,44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,68,68,68,68,68,68,0,0,0,68,68,68,68,68,68,0,0,0])))))) (TableTree.node 427 (TableTree.node 423 (TableTree.node 421 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,41,41,41,41,41,41,0,0,0,41,41,41,41,41,41,0,0,0])) (TableTree.node 422 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,68,68,68,68,68,68,0,0,0,68,68,68,68,68,68,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,41,41,41,41,41,41,0,0,0,41,41,41,41,41,41,0,0,0])))) (TableTree.node 425 (TableTree.node 424 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,42,42,42,42,42,0,0,0,42,42,42,42,42,42,0,0,0]))) (TableTree.node 426 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,42,42,42,42,42,0,0,0,42,42,42,42,42,42,0,0,0]))))) (TableTree.node 431 (TableTree.node 429 (TableTree.node 428 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,42,42,42,42,42,0,0,0,42,42,42,42,42,42,0,0,0]))) (TableTree.node 430 (TableTree.leaf (#[42,42,42,42,42,42,0,0,0,42,42,42,42,42,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[43,43,43,43,43,43,0,0,0,43,43,43,43,43,43,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])))) (TableTree.node 433 (TableTree.node 432 (TableTree.leaf (#[68,68,68,68,68,68,0,0,0,68,68,68,68,68,68,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[41,41,41,41,41,41,0,0,0,41,41,41,41,41,41,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))) (TableTree.node 434 (TableTree.leaf (#[41,41,41,41,41,41,0,0,0,0,0,0,0,0,0,0,0,0,41,41,41,41,41,41,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,41,41,41,41,41,41,0,0,0,41,41,41,41,41,41,0,0,0]))))))) (TableTree.node 449 (TableTree.node 442 (TableTree.node 438 (TableTree.node 436 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,41,41,41,41,41,41,0,0,0,41,41,41,41,41,41,0,0,0])) (TableTree.node 437 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0])) (TableTree.leaf (#[43,43,43,43,43,43,0,0,0,43,43,43,43,43,43,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])))) (TableTree.node 440 (TableTree.node 439 (TableTree.leaf (#[41,41,41,41,41,41,0,0,0,41,41,41,41,41,41,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))) (TableTree.node 441 (TableTree.leaf (#[42,42,42,42,42,42,0,0,0,42,42,42,42,42,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))))) (TableTree.node 445 (TableTree.node 443 (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.node 444 (TableTree.leaf (#[42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])))) (TableTree.node 447 (TableTree.node 446 (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))) (TableTree.node 448 (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])))))) (TableTree.node 456 (TableTree.node 452 (TableTree.node 450 (TableTree.leaf (#[43,43,43,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,43,43,43,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.node 451 (TableTree.leaf (#[44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])))) (TableTree.node 454 (TableTree.node 453 (TableTree.leaf (#[44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0]))) (TableTree.node 455 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0]))))) (TableTree.node 460 (TableTree.node 458 (TableTree.node 457 (TableTree.leaf (#[42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))) (TableTree.node 459 (TableTree.leaf (#[42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])))) (TableTree.node 462 (TableTree.node 461 (TableTree.leaf (#[43,43,43,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,43,43,43,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0]))) (TableTree.node 463 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0]))))))))))) (TableTree.node 696 (TableTree.node 580 (TableTree.node 522 (TableTree.node 493 (TableTree.node 478 (TableTree.node 471 (TableTree.node 467 (TableTree.node 465 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0])) (TableTree.node 466 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0])))) (TableTree.node 469 (TableTree.node 468 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0]))) (TableTree.node 470 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0]))))) (TableTree.node 474 (TableTree.node 472 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0])) (TableTree.node 473 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0])) (TableTree.leaf (#[42,42,42,42,42,42,0,0,0,42,42,42,42,42,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])))) (TableTree.node 476 (TableTree.node 475 (TableTree.leaf (#[42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[43,43,43,43,43,43,0,0,0,43,43,43,43,43,43,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))) (TableTree.node 477 (TableTree.leaf (#[43,43,43,0,0,0,0,0,0,43,43,43,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])))))) (TableTree.node 485 (TableTree.node 481 (TableTree.node 479 (TableTree.leaf (#[43,43,43,0,0,0,0,0,0,43,43,43,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.node 480 (TableTree.leaf (#[68,68,68,68,68,68,0,0,0,68,68,68,68,68,68,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[68,68,68,0,0,0,0,0,0,68,68,68,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])))) (TableTree.node 483 (TableTree.node 482 (TableTree.leaf (#[41,41,41,41,41,41,0,0,0,41,41,41,41,41,41,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[41,41,41,0,0,0,0,0,0,41,41,41,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))) (TableTree.node 484 (TableTree.leaf (#[68,68,68,0,0,0,0,0,0,68,68,68,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[41,41,41,0,0,0,0,0,0,41,41,41,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))))) (TableTree.node 489 (TableTree.node 487 (TableTree.node 486 (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))) (TableTree.node 488 (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])))) (TableTree.node 491 (TableTree.node 490 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,68,68,68,0,0,0,0,0,0,68,68,68,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,41,41,41,0,0,0,0,0,0,41,41,41,0,0,0,0,0,0]))) (TableTree.node 492 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,68,68,68,0,0,0,0,0,0,68,68,68,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,41,41,41,0,0,0,0,0,0,41,41,41,0,0,0,0,0,0]))))))) (TableTree.node 507 (TableTree.node 500 (TableTree.node 496 (TableTree.node 494 (TableTree.leaf (#[41,41,41,0,0,0,0,0,0,41,41,41,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.node 495 (TableTree.leaf (#[41,41,41,0,0,0,0,0,0,41,41,41,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[41,41,41,0,0,0,0,0,0,41,41,41,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])))) (TableTree.node 498 (TableTree.node 497 (TableTree.leaf (#[41,41,41,0,0,0,0,0,0,41,41,41,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))) (TableTree.node 499 (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0]))))) (TableTree.node 503 (TableTree.node 501 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0])) (TableTree.node 502 (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0])))) (TableTree.node 505 (TableTree.node 504 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0]))) (TableTree.node 506 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,43,43,43,0,0,0,0,0,0,43,43,43,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,43,43,43,0,0,0,0,0,0,43,43,43,0,0,0,0,0,0])))))) (TableTree.node 514 (TableTree.node 510 (TableTree.node 508 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0])) (TableTree.node 509 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,43,43,43,0,0,0,0,0,0,43,43,43,0,0,0,0,0,0])) (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0])))) (TableTree.node 512 (TableTree.node 511 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0]))) (TableTree.node 513 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0]))))) (TableTree.node 518 (TableTree.node 516 (TableTree.node 515 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0])) (TableTree.leaf (#[42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))) (TableTree.node 517 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0])) (TableTree.leaf (#[42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])))) (TableTree.node 520 (TableTree.node 519 (TableTree.leaf (#[43,43,43,0,0,0,0,0,0,43,43,43,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))) (TableTree.node 521 (TableTree.leaf (#[43,43,43,0,0,0,0,0,0,43,43,43,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0])))))))) (TableTree.node 551 (TableTree.node 536 (TableTree.node 529 (TableTree.node 525 (TableTree.node 523 (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.node 524 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0])))) (TableTree.node 527 (TableTree.node 526 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,43,43,43,0,0,0,0,0,0,43,43,43,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,68,68,68,0,0,0,0,0,0,68,68,68,0,0,0,0,0,0]))) (TableTree.node 528 (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[42,42,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))))) (TableTree.node 532 (TableTree.node 530 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0])) (TableTree.node 531 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,43,43,43,0,0,0,0,0,0,43,43,43,0,0,0,0,0,0])))) (TableTree.node 534 (TableTree.node 533 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0]))) (TableTree.node 535 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0])))))) (TableTree.node 543 (TableTree.node 539 (TableTree.node 537 (TableTree.leaf (#[42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.node 538 (TableTree.leaf (#[43,43,43,0,0,0,0,0,0,43,43,43,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[42,42,42,42,42,42,0,0,0,42,42,42,42,42,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])))) (TableTree.node 541 (TableTree.node 540 (TableTree.leaf (#[42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[43,43,43,43,43,43,0,0,0,43,43,43,43,43,43,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))) (TableTree.node 542 (TableTree.leaf (#[43,43,43,0,0,0,0,0,0,43,43,43,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))))) (TableTree.node 547 (TableTree.node 545 (TableTree.node 544 (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))) (TableTree.node 546 (TableTree.leaf (#[43,43,43,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,43,43,43,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,68,68,68,0,0,0,0,0,0,68,68,68,0,0,0,0,0,0])))) (TableTree.node 549 (TableTree.node 548 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,41,41,41,0,0,0,0,0,0,41,41,41,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,41,41,41,0,0,0,0,0,0,41,41,41,0,0,0,0,0,0]))) (TableTree.node 550 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,41,41,41,0,0,0,0,0,0,41,41,41,0,0,0,0,0,0])) (TableTree.leaf (#[41,41,41,0,0,0,0,0,0,41,41,41,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))))))) (TableTree.node 565 (TableTree.node 558 (TableTree.node 554 (TableTree.node 552 (TableTree.leaf (#[41,41,41,0,0,0,0,0,0,41,41,41,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.node 553 (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])))) (TableTree.node 556 (TableTree.node 555 (TableTree.leaf (#[43,43,43,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,43,43,43,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,43,43,43,0,0,0,0,0,0,43,43,43,0,0,0,0,0,0]))) (TableTree.node 557 (TableTree.leaf (#[44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))))) (TableTree.node 561 (TableTree.node 559 (TableTree.leaf (#[42,42,42,42,42,42,0,0,0,42,42,42,42,42,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.node 560 (TableTree.leaf (#[42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])))) (TableTree.node 563 (TableTree.node 562 (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))) (TableTree.node 564 (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0])))))) (TableTree.node 572 (TableTree.node 568 (TableTree.node 566 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0])) (TableTree.node 567 (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0])))) (TableTree.node 570 (TableTree.node 569 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,43,43,43,0,0,0,0,0,0,43,43,43,0,0,0,0,0,0]))) (TableTree.node 571 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,68,68,68,0,0,0,0,0,0,68,68,68,0,0,0,0,0,0])) (TableTree.leaf (#[41,41,41,0,0,0,0,0,0,41,41,41,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))))) (TableTree.node 576 (TableTree.node 574 (TableTree.node 573 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0]))) (TableTree.node 575 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0])))) (TableTree.node 578 (TableTree.node 577 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0]))) (TableTree.node 579 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0]))))))))) (TableTree.node 638 (TableTree.node 609 (TableTree.node 594 (TableTree.node 587 (TableTree.node 583 (TableTree.node 581 (TableTree.leaf (#[42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.node 582 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0])) (TableTree.leaf (#[42,42,42,42,42,42,0,0,0,42,42,42,42,42,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])))) (TableTree.node 585 (TableTree.node 584 (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))) (TableTree.node 586 (TableTree.leaf (#[42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[43,43,43,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,43,43,43,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))))) (TableTree.node 590 (TableTree.node 588 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,43,43,43,0,0,0,0,0,0,43,43,43,0,0,0,0,0,0])) (TableTree.node 589 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,43,43,43,0,0,0,0,0,0,43,43,43,0,0,0,0,0,0])))) (TableTree.node 592 (TableTree.node 591 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,68,68,68,0,0,0,0,0,0,68,68,68,0,0,0,0,0,0])) (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))) (TableTree.node 593 (TableTree.leaf (#[42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])))))) (TableTree.node 601 (TableTree.node 597 (TableTree.node 595 (TableTree.leaf (#[43,43,43,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,43,43,43,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.node 596 (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])))) (TableTree.node 599 (TableTree.node 598 (TableTree.leaf (#[44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))) (TableTree.node 600 (TableTree.leaf (#[44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))))) (TableTree.node 605 (TableTree.node 603 (TableTree.node 602 (TableTree.leaf (#[42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[43,43,43,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,43,43,43,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))) (TableTree.node 604 (TableTree.leaf (#[44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])))) (TableTree.node 607 (TableTree.node 606 (TableTree.leaf (#[44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0]))) (TableTree.node 608 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0]))))))) (TableTree.node 623 (TableTree.node 616 (TableTree.node 612 (TableTree.node 610 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,43,43,43,0,0,0,0,0,0,43,43,43,0,0,0,0,0,0])) (TableTree.node 611 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,43,43,43,0,0,0,0,0,0,43,43,43,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0])))) (TableTree.node 614 (TableTree.node 613 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0]))) (TableTree.node 615 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0]))))) (TableTree.node 619 (TableTree.node 617 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0])) (TableTree.node 618 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0])))) (TableTree.node 621 (TableTree.node 620 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0]))) (TableTree.node 622 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0])))))) (TableTree.node 630 (TableTree.node 626 (TableTree.node 624 (TableTree.leaf (#[41,41,41,0,0,0,0,0,0,41,41,41,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.node 625 (TableTree.leaf (#[41,41,41,0,0,0,0,0,0,41,41,41,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[41,41,41,0,0,0,0,0,0,41,41,41,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])))) (TableTree.node 628 (TableTree.node 627 (TableTree.leaf (#[41,41,41,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,41,41,41,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,41,41,41,0,0,0,0,0,0,41,41,41,0,0,0,0,0,0]))) (TableTree.node 629 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,41,41,41,0,0,0,0,0,0,41,41,41,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,41,41,41,0,0,0,0,0,0,41,41,41,0,0,0,0,0,0]))))) (TableTree.node 634 (TableTree.node 632 (TableTree.node 631 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,41,41,41,0,0,0,0,0,0,41,41,41,0,0,0,0,0,0])) (TableTree.leaf (#[43,43,43,43,43,43,0,0,0,43,43,43,43,43,43,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))) (TableTree.node 633 (TableTree.leaf (#[43,43,43,0,0,0,0,0,0,43,43,43,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])))) (TableTree.node 636 (TableTree.node 635 (TableTree.leaf (#[42,42,42,42,42,42,0,0,0,42,42,42,42,42,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))) (TableTree.node 637 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0])))))))) (TableTree.node 667 (TableTree.node 652 (TableTree.node 645 (TableTree.node 641 (TableTree.node 639 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0])) (TableTree.node 640 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0])))) (TableTree.node 643 (TableTree.node 642 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0])) (TableTree.leaf (#[42,42,42,42,42,42,0,0,0,42,42,42,42,42,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))) (TableTree.node 644 (TableTree.leaf (#[42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[43,43,43,43,43,43,0,0,0,43,43,43,43,43,43,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))))) (TableTree.node 648 (TableTree.node 646 (TableTree.leaf (#[43,43,43,0,0,0,0,0,0,43,43,43,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.node 647 (TableTree.leaf (#[42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[43,43,43,0,0,0,0,0,0,43,43,43,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])))) (TableTree.node 650 (TableTree.node 649 (TableTree.leaf (#[68,68,68,68,68,68,0,0,0,68,68,68,68,68,68,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[68,68,68,0,0,0,0,0,0,68,68,68,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))) (TableTree.node 651 (TableTree.leaf (#[41,41,41,41,41,41,0,0,0,41,41,41,41,41,41,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[41,41,41,0,0,0,0,0,0,41,41,41,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])))))) (TableTree.node 659 (TableTree.node 655 (TableTree.node 653 (TableTree.leaf (#[68,68,68,0,0,0,0,0,0,68,68,68,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.node 654 (TableTree.leaf (#[41,41,41,0,0,0,0,0,0,41,41,41,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])))) (TableTree.node 657 (TableTree.node 656 (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))) (TableTree.node 658 (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))))) (TableTree.node 663 (TableTree.node 661 (TableTree.node 660 (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0]))) (TableTree.node 662 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0])) (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])))) (TableTree.node 665 (TableTree.node 664 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0]))) (TableTree.node 666 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,43,43,43,0,0,0,0,0,0,43,43,43,0,0,0,0,0,0]))))))) (TableTree.node 681 (TableTree.node 674 (TableTree.node 670 (TableTree.node 668 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,43,43,43,0,0,0,0,0,0,43,43,43,0,0,0,0,0,0])) (TableTree.node 669 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,43,43,43,0,0,0,0,0,0,43,43,43,0,0,0,0,0,0])))) (TableTree.node 672 (TableTree.node 671 (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0]))) (TableTree.node 673 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0]))))) (TableTree.node 677 (TableTree.node 675 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0])) (TableTree.node 676 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0])) (TableTree.leaf (#[42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])))) (TableTree.node 679 (TableTree.node 678 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0])) (TableTree.leaf (#[42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))) (TableTree.node 680 (TableTree.leaf (#[43,43,43,0,0,0,0,0,0,43,43,43,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])))))) (TableTree.node 688 (TableTree.node 684 (TableTree.node 682 (TableTree.leaf (#[43,43,43,0,0,0,0,0,0,43,43,43,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.node 683 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0])) (TableTree.leaf (#[42,42,42,42,42,42,0,0,0,42,42,42,42,42,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])))) (TableTree.node 686 (TableTree.node 685 (TableTree.leaf (#[44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))) (TableTree.node 687 (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[42,42,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))))) (TableTree.node 692 (TableTree.node 690 (TableTree.node 689 (TableTree.leaf (#[44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0]))) (TableTree.node 691 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,43,43,43,0,0,0,0,0,0,43,43,43,0,0,0,0,0,0])))) (TableTree.node 694 (TableTree.node 693 (TableTree.leaf (#[44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))) (TableTree.node 695 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0])))))))))) (TableTree.node 812 (TableTree.node 754 (TableTree.node 725 (TableTree.node 710 (TableTree.node 703 (TableTree.node 699 (TableTree.node 697 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0])) (TableTree.node 698 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0])))) (TableTree.node 701 (TableTree.node 700 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0])) (TableTree.leaf (#[42,42,42,42,42,42,0,0,0,42,42,42,42,42,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))) (TableTree.node 702 (TableTree.leaf (#[43,43,43,43,43,43,0,0,0,43,43,43,43,43,43,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0]))))) (TableTree.node 706 (TableTree.node 704 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0])) (TableTree.node 705 (TableTree.leaf (#[44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[42,42,42,42,42,42,0,0,0,42,42,42,42,42,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])))) (TableTree.node 708 (TableTree.node 707 (TableTree.leaf (#[43,43,43,43,43,43,0,0,0,0,0,0,0,0,0,0,0,0,43,43,43,43,43,43,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,43,43,43,43,43,43,0,0,0,43,43,43,43,43,43,0,0,0]))) (TableTree.node 709 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,42,42,42,42,42,0,0,0,42,42,42,42,42,42,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,43,43,43,43,43,43,0,0,0,43,43,43,43,43,43,0,0,0])))))) (TableTree.node 717 (TableTree.node 713 (TableTree.node 711 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,68,68,68,68,68,68,0,0,0,68,68,68,68,68,68,0,0,0])) (TableTree.node 712 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,43,43,43,43,43,43,0,0,0,43,43,43,43,43,43,0,0,0])))) (TableTree.node 715 (TableTree.node 714 (TableTree.leaf (#[42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[43,43,43,0,0,0,0,0,0,43,43,43,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))) (TableTree.node 716 (TableTree.leaf (#[68,68,68,0,0,0,0,0,0,68,68,68,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[41,41,41,0,0,0,0,0,0,41,41,41,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))))) (TableTree.node 721 (TableTree.node 719 (TableTree.node 718 (TableTree.leaf (#[41,41,41,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,41,41,41,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,41,41,41,0,0,0,0,0,0,41,41,41,0,0,0,0,0,0]))) (TableTree.node 720 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,41,41,41,0,0,0,0,0,0,41,41,41,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,41,41,41,0,0,0,0,0,0,41,41,41,0,0,0,0,0,0])))) (TableTree.node 723 (TableTree.node 722 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0])) (TableTree.leaf (#[41,41,41,0,0,0,0,0,0,41,41,41,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))) (TableTree.node 724 (TableTree.leaf (#[41,41,41,0,0,0,0,0,0,41,41,41,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[41,41,41,0,0,0,0,0,0,41,41,41,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))))))) (TableTree.node 739 (TableTree.node 732 (TableTree.node 728 (TableTree.node 726 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0])) (TableTree.node 727 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0])) (TableTree.leaf (#[68,68,68,68,68,68,68,68,68,68,68,68,68,68,68,68,68,68,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])))) (TableTree.node 730 (TableTree.node 729 (TableTree.leaf (#[68,68,68,68,68,68,0,0,0,68,68,68,68,68,68,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[41,41,41,41,41,41,41,41,41,41,41,41,41,41,41,41,41,41,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))) (TableTree.node 731 (TableTree.leaf (#[41,41,41,41,41,41,0,0,0,41,41,41,41,41,41,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[68,68,68,68,68,68,0,0,0,68,68,68,68,68,68,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))))) (TableTree.node 735 (TableTree.node 733 (TableTree.leaf (#[41,41,41,41,41,41,0,0,0,41,41,41,41,41,41,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.node 734 (TableTree.leaf (#[44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,42,42,42,42,42,0,0,0,42,42,42,42,42,42,0,0,0])))) (TableTree.node 737 (TableTree.node 736 (TableTree.leaf (#[68,68,68,68,68,68,0,0,0,68,68,68,68,68,68,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0]))) (TableTree.node 738 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,42,42,42,42,42,0,0,0,42,42,42,42,42,42,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,43,43,43,43,43,43,0,0,0,43,43,43,43,43,43,0,0,0])))))) (TableTree.node 746 (TableTree.node 742 (TableTree.node 740 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,43,43,43,43,43,43,0,0,0,43,43,43,43,43,43,0,0,0])) (TableTree.node 741 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0])) (TableTree.leaf (#[42,42,42,42,42,42,0,0,0,42,42,42,42,42,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])))) (TableTree.node 744 (TableTree.node 743 (TableTree.leaf (#[43,43,43,43,43,43,0,0,0,43,43,43,43,43,43,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[42,42,42,42,42,42,0,0,0,42,42,42,42,42,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))) (TableTree.node 745 (TableTree.leaf (#[44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[42,42,42,42,42,42,0,0,0,0,0,0,0,0,0,0,0,0,42,42,42,42,42,42,0,0,0,0,0,0,0,0,0,0,0,0]))))) (TableTree.node 750 (TableTree.node 748 (TableTree.node 747 (TableTree.leaf (#[44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,43,43,43,43,43,43,0,0,0,43,43,43,43,43,43,0,0,0]))) (TableTree.node 749 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,42,42,42,42,42,0,0,0,42,42,42,42,42,42,0,0,0])) (TableTree.leaf (#[68,68,68,68,68,68,0,0,0,0,0,0,0,0,0,0,0,0,68,68,68,68,68,68,0,0,0,0,0,0,0,0,0,0,0,0])))) (TableTree.node 752 (TableTree.node 751 (TableTree.leaf (#[42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[43,43,43,0,0,0,0,0,0,43,43,43,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))) (TableTree.node 753 (TableTree.leaf (#[68,68,68,68,68,68,0,0,0,68,68,68,68,68,68,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[68,68,68,0,0,0,0,0,0,68,68,68,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])))))))) (TableTree.node 783 (TableTree.node 768 (TableTree.node 761 (TableTree.node 757 (TableTree.node 755 (TableTree.leaf (#[41,41,41,41,41,41,0,0,0,41,41,41,41,41,41,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.node 756 (TableTree.leaf (#[41,41,41,0,0,0,0,0,0,41,41,41,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[68,68,68,0,0,0,0,0,0,68,68,68,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])))) (TableTree.node 759 (TableTree.node 758 (TableTree.leaf (#[41,41,41,0,0,0,0,0,0,41,41,41,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[41,41,41,41,41,41,0,0,0,0,0,0,0,0,0,0,0,0,41,41,41,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))) (TableTree.node 760 (TableTree.leaf (#[41,41,41,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,41,41,41,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,41,41,41,0,0,0,0,0,0,41,41,41,0,0,0,0,0,0]))))) (TableTree.node 764 (TableTree.node 762 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,41,41,41,0,0,0,0,0,0,41,41,41,0,0,0,0,0,0])) (TableTree.node 763 (TableTree.leaf (#[41,41,41,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,41,41,41,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,41,41,41,0,0,0,0,0,0,41,41,41,0,0,0,0,0,0])))) (TableTree.node 766 (TableTree.node 765 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,41,41,41,0,0,0,0,0,0,41,41,41,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,41,41,41,0,0,0,0,0,0,41,41,41,0,0,0,0,0,0]))) (TableTree.node 767 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,41,41,41,0,0,0,0,0,0,41,41,41,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,41,41,41,0,0,0,0,0,0,41,41,41,0,0,0,0,0,0])))))) (TableTree.node 775 (TableTree.node 771 (TableTree.node 769 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,41,41,41,0,0,0,0,0,0,41,41,41,0,0,0,0,0,0])) (TableTree.node 770 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,41,41,41,0,0,0,0,0,0,41,41,41,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0])))) (TableTree.node 773 (TableTree.node 772 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,68,68,68,68,68,68,0,0,0,68,68,68,68,68,68,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,41,41,41,41,41,41,0,0,0,41,41,41,41,41,41,0,0,0]))) (TableTree.node 774 (TableTree.leaf (#[42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[43,43,43,0,0,0,0,0,0,43,43,43,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))))) (TableTree.node 779 (TableTree.node 777 (TableTree.node 776 (TableTree.leaf (#[68,68,68,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,68,68,68,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[43,43,43,0,0,0,0,0,0,43,43,43,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))) (TableTree.node 778 (TableTree.leaf (#[68,68,68,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,68,68,68,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0])))) (TableTree.node 781 (TableTree.node 780 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0,44,44,44,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0,42,42,42,0,0,0,0,0,0]))) (TableTree.node 782 (TableTree.leaf (#[43,43,43,43,43,43,0,0,0,43,43,43,43,43,43,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[68,68,68,68,68,68,0,0,0,68,68,68,68,68,68,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))))))) (TableTree.node 797 (TableTree.node 790 (TableTree.node 786 (TableTree.node 784 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,68,68,68,0,0,0,0,0,0,68,68,68,0,0,0,0,0,0])) (TableTree.node 785 (TableTree.leaf (#[41,41,41,41,41,41,41,41,41,0,0,0,0,0,0,0,0,0,41,41,41,41,41,41,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[41,41,41,41,41,41,0,0,0,0,0,0,0,0,0,0,0,0,41,41,41,41,41,41,0,0,0,0,0,0,0,0,0,0,0,0])))) (TableTree.node 788 (TableTree.node 787 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,41,41,41,41,41,41,0,0,0,41,41,41,41,41,41,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,41,41,41,41,41,41,0,0,0,41,41,41,41,41,41,0,0,0]))) (TableTree.node 789 (TableTree.leaf (#[41,41,41,41,41,41,0,0,0,0,0,0,0,0,0,0,0,0,41,41,41,41,41,41,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,41,41,41,41,41,41,0,0,0,41,41,41,41,41,41,0,0,0]))))) (TableTree.node 793 (TableTree.node 791 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,41,41,41,41,41,41,0,0,0,41,41,41,41,41,41,0,0,0])) (TableTree.node 792 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,41,41,41,41,41,41,0,0,0,41,41,41,41,41,41,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,41,41,41,41,41,41,0,0,0,41,41,41,41,41,41,0,0,0])))) (TableTree.node 795 (TableTree.node 794 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,41,41,41,41,41,41,0,0,0,41,41,41,41,41,41,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,41,41,41,41,41,41,0,0,0,41,41,41,41,41,41,0,0,0]))) (TableTree.node 796 (TableTree.leaf (#[42,42,42,42,42,42,0,0,0,42,42,42,42,42,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[43,43,43,43,43,43,0,0,0,43,43,43,43,43,43,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])))))) (TableTree.node 804 (TableTree.node 800 (TableTree.node 798 (TableTree.leaf (#[68,68,68,68,68,68,0,0,0,0,0,0,0,0,0,0,0,0,68,68,68,68,68,68,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.node 799 (TableTree.leaf (#[43,43,43,43,43,43,0,0,0,43,43,43,43,43,43,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0])))) (TableTree.node 802 (TableTree.node 801 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,42,42,42,42,42,0,0,0,42,42,42,42,42,42,0,0,0]))) (TableTree.node 803 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,41,41,41,41,41,41,0,0,0,41,41,41,41,41,41,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,41,41,41,41,41,41,0,0,0,41,41,41,41,41,41,0,0,0]))))) (TableTree.node 808 (TableTree.node 806 (TableTree.node 805 (TableTree.leaf (#[41,41,41,41,41,41,0,0,0,41,41,41,41,41,41,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,41,41,41,41,41,41,0,0,0,41,41,41,41,41,41,0,0,0]))) (TableTree.node 807 (TableTree.leaf (#[41,41,41,41,41,41,0,0,0,41,41,41,41,41,41,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[41,41,41,41,41,41,0,0,0,41,41,41,41,41,41,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])))) (TableTree.node 810 (TableTree.node 809 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,68,68,68,68,68,68,0,0,0,68,68,68,68,68,68,0,0,0])) (TableTree.leaf (#[41,41,41,41,41,41,0,0,0,41,41,41,41,41,41,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))) (TableTree.node 811 (TableTree.leaf (#[41,41,41,41,41,41,0,0,0,41,41,41,41,41,41,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[41,41,41,41,41,41,0,0,0,41,41,41,41,41,41,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))))))))) (TableTree.node 870 (TableTree.node 841 (TableTree.node 826 (TableTree.node 819 (TableTree.node 815 (TableTree.node 813 (TableTree.leaf (#[72,72,72,0,0,0,0,0,0,72,72,72,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.node 814 (TableTree.leaf (#[72,72,72,0,0,0,0,0,0,72,72,72,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[72,72,72,0,0,0,0,0,0,72,72,72,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])))) (TableTree.node 817 (TableTree.node 816 (TableTree.leaf (#[72,72,72,0,0,0,0,0,0,72,72,72,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[72,72,72,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,72,72,72,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))) (TableTree.node 818 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,72,72,72,0,0,0,0,0,0,72,72,72,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,72,72,72,0,0,0,0,0,0,72,72,72,0,0,0,0,0,0]))))) (TableTree.node 822 (TableTree.node 820 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,72,72,72,0,0,0,0,0,0,72,72,72,0,0,0,0,0,0])) (TableTree.node 821 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,72,72,72,0,0,0,0,0,0,72,72,72,0,0,0,0,0,0])) (TableTree.leaf (#[42,72,72,42,72,72,42,42,42,42,42,42,42,42,42,42,42,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])))) (TableTree.node 824 (TableTree.node 823 (TableTree.leaf (#[42,72,72,42,42,42,0,0,0,42,42,42,42,42,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[44,72,72,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))) (TableTree.node 825 (TableTree.leaf (#[44,72,72,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[44,72,72,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])))))) (TableTree.node 833 (TableTree.node 829 (TableTree.node 827 (TableTree.leaf (#[42,72,72,42,42,42,0,0,0,42,42,42,42,42,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.node 828 (TableTree.leaf (#[44,72,72,44,72,72,44,44,44,44,72,72,44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[44,72,72,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])))) (TableTree.node 831 (TableTree.node 830 (TableTree.leaf (#[42,72,72,42,72,72,42,42,42,42,42,42,42,42,42,42,42,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[42,72,72,42,42,42,0,0,0,42,42,42,42,42,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))) (TableTree.node 832 (TableTree.leaf (#[44,72,72,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[44,72,72,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))))) (TableTree.node 837 (TableTree.node 835 (TableTree.node 834 (TableTree.leaf (#[44,72,72,44,72,72,44,44,44,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[44,72,72,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0]))) (TableTree.node 836 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,42,42,42,42,42,0,0,0,42,72,72,42,42,42,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,42,42,42,42,42,0,0,0,42,72,72,42,42,42,0,0,0])))) (TableTree.node 839 (TableTree.node 838 (TableTree.leaf (#[44,72,72,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,44,44,44,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,44,44,44,44,72,72,44,72,72,44,44,44]))) (TableTree.node 840 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,42,42,42,42,42,0,0,0,42,72,72,42,42,42,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,44,72,72,44,44,44,0,0,0]))))))) (TableTree.node 855 (TableTree.node 848 (TableTree.node 844 (TableTree.node 842 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,44,72,72,44,44,44,0,0,0])) (TableTree.node 843 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,44,72,72,44,44,44,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,42,42,42,42,42,0,0,0,42,72,72,42,42,42,0,0,0])))) (TableTree.node 846 (TableTree.node 845 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,44,44,44,44,72,72,44,72,72,44,44,44])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,44,44,44,44,72,72,44,72,72,44,44,44]))) (TableTree.node 847 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,44,72,72,44,44,44,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,44,72,72,44,44,44,0,0,0]))))) (TableTree.node 851 (TableTree.node 849 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,44,44,44,44,72,72,44,72,72,44,44,44])) (TableTree.node 850 (TableTree.leaf (#[44,72,72,44,44,44,0,0,0,44,72,72,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[42,42,42,42,42,42,0,0,0,42,42,42,42,42,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])))) (TableTree.node 853 (TableTree.node 852 (TableTree.leaf (#[44,72,72,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[42,42,42,42,42,42,0,0,0,42,42,42,42,42,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))) (TableTree.node 854 (TableTree.leaf (#[44,72,72,44,72,72,44,44,44,44,72,72,44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[44,72,72,44,72,72,44,44,44,44,44,44,44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])))))) (TableTree.node 862 (TableTree.node 858 (TableTree.node 856 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,44,72,72,44,44,44,0,0,0])) (TableTree.node 857 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,42,42,42,42,42,0,0,0,42,72,72,42,42,42,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,44,72,72,44,44,44,0,0,0])))) (TableTree.node 860 (TableTree.node 859 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,42,42,42,42,42,0,0,0,42,72,72,42,42,42,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,72,72,44,44,44,0,0,0,44,72,72,44,44,44,0,0,0]))) (TableTree.node 861 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,42,42,42,42,42,0,0,0,42,42,42,42,42,42,0,0,0])) (TableTree.leaf (#[42,72,72,42,42,42,0,0,0,42,42,42,42,42,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))))) (TableTree.node 866 (TableTree.node 864 (TableTree.node 863 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,44,72,72,44,44,44,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,44,72,72,44,44,44,0,0,0]))) (TableTree.node 865 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,72,72,44,44,44,0,0,0,44,72,72,44,44,44,0,0,0])) (TableTree.leaf (#[42,72,72,42,42,42,0,0,0,42,42,42,42,42,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])))) (TableTree.node 868 (TableTree.node 867 (TableTree.leaf (#[44,72,72,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[42,72,72,42,42,42,0,0,0,42,42,42,42,42,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))) (TableTree.node 869 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,42,42,42,42,42,0,0,0,42,72,72,42,42,42,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,44,72,72,44,44,44,0,0,0])))))))) (TableTree.node 899 (TableTree.node 884 (TableTree.node 877 (TableTree.node 873 (TableTree.node 871 (TableTree.leaf (#[44,72,72,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.node 872 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,42,42,42,42,42,0,0,0,42,42,42,42,42,42,0,0,0])) (TableTree.leaf (#[44,72,72,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0])))) (TableTree.node 875 (TableTree.node 874 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,42,42,42,42,42,0,0,0,42,72,72,42,42,42,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,44,72,72,44,44,44,0,0,0]))) (TableTree.node 876 (TableTree.leaf (#[42,72,72,42,42,42,0,0,0,42,42,42,42,42,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[42,72,72,42,42,42,0,0,0,42,42,42,42,42,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))))) (TableTree.node 880 (TableTree.node 878 (TableTree.leaf (#[44,72,72,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.node 879 (TableTree.leaf (#[42,72,72,42,42,42,0,0,0,0,0,0,0,0,0,0,0,0,42,42,42,42,42,42,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[44,72,72,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])))) (TableTree.node 882 (TableTree.node 881 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,42,42,42,42,42,0,0,0,42,42,42,42,42,42,0,0,0])) (TableTree.leaf (#[42,42,42,42,42,42,0,0,0,42,42,42,42,42,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))) (TableTree.node 883 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,44,72,72,44,44,44,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,72,72,44,44,44,0,0,0,44,72,72,44,44,44,0,0,0])))))) (TableTree.node 891 (TableTree.node 887 (TableTree.node 885 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,42,42,42,42,42,0,0,0,42,42,42,42,42,42,0,0,0])) (TableTree.node 886 (TableTree.leaf (#[42,44,42,42,42,42,0,0,0,42,42,42,42,42,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[42,44,44,44,44,44,0,0,0,44,72,72,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])))) (TableTree.node 889 (TableTree.node 888 (TableTree.leaf (#[42,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[42,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))) (TableTree.node 890 (TableTree.leaf (#[42,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,42,44,44,44,44,44,0,0,0]))))) (TableTree.node 895 (TableTree.node 893 (TableTree.node 892 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,42,44,44,44,44,44,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,72,72,44,44,44,0,0,0,42,44,44,44,44,44,0,0,0]))) (TableTree.node 894 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,42,44,44,44,44,44,0,0,0])) (TableTree.leaf (#[42,72,72,42,44,42,42,42,42,42,42,42,42,42,42,42,42,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])))) (TableTree.node 897 (TableTree.node 896 (TableTree.leaf (#[42,44,44,42,44,44,44,44,44,44,72,72,44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[42,44,44,42,44,44,44,44,44,44,72,72,44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))) (TableTree.node 898 (TableTree.leaf (#[42,44,44,42,44,44,44,44,44,44,44,44,44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[42,44,44,42,44,44,44,44,44,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0]))))))) (TableTree.node 914 (TableTree.node 906 (TableTree.node 902 (TableTree.node 900 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,42,44,44,44,44,44,0,0,0])) (TableTree.node 901 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,42,44,44,44,44,44,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,42,44,44,44,44,44,0,0,0])))) (TableTree.node 904 (TableTree.node 903 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,42,44,44,44,44,44,0,0,0])) (TableTree.leaf (#[42,44,42,42,42,42,0,0,0,42,42,42,42,42,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))) (TableTree.node 905 (TableTree.leaf (#[42,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[42,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))))) (TableTree.node 910 (TableTree.node 908 (TableTree.node 907 (TableTree.leaf (#[42,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[42,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0]))) (TableTree.node 909 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,42,44,44,44,44,44,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,42,44,44,44,44,44,0,0,0])))) (TableTree.node 912 (TableTree.node 911 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,72,72,44,44,44,0,0,0,42,44,44,44,44,44,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,42,44,44,44,44,44,0,0,0]))) (TableTree.node 913 (TableTree.leaf (#[42,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[42,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])))))) (TableTree.node 921 (TableTree.node 917 (TableTree.node 915 (TableTree.leaf (#[42,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.node 916 (TableTree.leaf (#[42,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[42,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,44,44,44,0,0,0,0,0,0,0,0,0])))) (TableTree.node 919 (TableTree.node 918 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,44,44,44,42,44,44,42,44,44,44,44,44])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,44,44,44,42,44,44,42,44,44,44,44,44]))) (TableTree.node 920 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,44,44,44,42,44,44,42,44,44,44,44,44])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,44,44,44,42,44,44,42,44,44,44,44,44]))))) (TableTree.node 925 (TableTree.node 923 (TableTree.node 922 (TableTree.leaf (#[42,72,72,42,42,42,0,0,0,42,42,42,42,42,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[42,44,44,44,44,44,0,0,0,44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]))) (TableTree.node 924 (TableTree.leaf (#[42,72,72,42,42,42,0,0,0,42,42,42,42,42,42,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0])) (TableTree.leaf (#[42,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,0,0,0,0,0,0,0,0,0])))) (TableTree.node 927 (TableTree.node 926 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,42,42,42,42,42,0,0,0,42,72,72,42,42,42,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,42,44,44,44,44,44,0,0,0]))) (TableTree.node 928 (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,72,72,44,44,44,0,0,0,42,44,44,44,44,44,0,0,0])) (TableTree.leaf (#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,44,44,44,44,44,0,0,0,42,44,44,44,44,44,0,0,0]))))))))))))
private def parentAt (i : ℕ) : (Array ℕ) := if i < 929 then TableTree.lookup parentAtTree i else #[]
private def finishAtTree : TableTree (ℕ) := (TableTree.node 464 (TableTree.node 232 (TableTree.node 116 (TableTree.node 58 (TableTree.node 29 (TableTree.node 14 (TableTree.node 7 (TableTree.node 3 (TableTree.node 1 (TableTree.leaf (0)) (TableTree.node 2 (TableTree.leaf (1)) (TableTree.leaf (0)))) (TableTree.node 5 (TableTree.node 4 (TableTree.leaf (3)) (TableTree.leaf (5))) (TableTree.node 6 (TableTree.leaf (0)) (TableTree.leaf (0))))) (TableTree.node 10 (TableTree.node 8 (TableTree.leaf (0)) (TableTree.node 9 (TableTree.leaf (0)) (TableTree.leaf (15)))) (TableTree.node 12 (TableTree.node 11 (TableTree.leaf (18)) (TableTree.leaf (0))) (TableTree.node 13 (TableTree.leaf (21)) (TableTree.leaf (23)))))) (TableTree.node 21 (TableTree.node 17 (TableTree.node 15 (TableTree.leaf (0)) (TableTree.node 16 (TableTree.leaf (0)) (TableTree.leaf (0)))) (TableTree.node 19 (TableTree.node 18 (TableTree.leaf (0)) (TableTree.leaf (39))) (TableTree.node 20 (TableTree.leaf (20)) (TableTree.leaf (0))))) (TableTree.node 25 (TableTree.node 23 (TableTree.node 22 (TableTree.leaf (35)) (TableTree.leaf (44))) (TableTree.node 24 (TableTree.leaf (0)) (TableTree.leaf (0)))) (TableTree.node 27 (TableTree.node 26 (TableTree.leaf (0)) (TableTree.leaf (0))) (TableTree.node 28 (TableTree.leaf (47)) (TableTree.leaf (46))))))) (TableTree.node 43 (TableTree.node 36 (TableTree.node 32 (TableTree.node 30 (TableTree.leaf (54)) (TableTree.node 31 (TableTree.leaf (54)) (TableTree.leaf (0)))) (TableTree.node 34 (TableTree.node 33 (TableTree.leaf (0)) (TableTree.leaf (58))) (TableTree.node 35 (TableTree.leaf (58)) (TableTree.leaf (60))))) (TableTree.node 39 (TableTree.node 37 (TableTree.leaf (59)) (TableTree.node 38 (TableTree.leaf (0)) (TableTree.leaf (0)))) (TableTree.node 41 (TableTree.node 40 (TableTree.leaf (0)) (TableTree.leaf (0))) (TableTree.node 42 (TableTree.leaf (0)) (TableTree.leaf (0)))))) (TableTree.node 50 (TableTree.node 46 (TableTree.node 44 (TableTree.leaf (0)) (TableTree.node 45 (TableTree.leaf (0)) (TableTree.leaf (69)))) (TableTree.node 48 (TableTree.node 47 (TableTree.leaf (21)) (TableTree.leaf (0))) (TableTree.node 49 (TableTree.leaf (44)) (TableTree.leaf (20))))) (TableTree.node 54 (TableTree.node 52 (TableTree.node 51 (TableTree.leaf (0)) (TableTree.leaf (0))) (TableTree.node 53 (TableTree.leaf (0)) (TableTree.leaf (0)))) (TableTree.node 56 (TableTree.node 55 (TableTree.leaf (42)) (TableTree.leaf (44))) (TableTree.node 57 (TableTree.leaf (44)) (TableTree.leaf (44)))))))) (TableTree.node 87 (TableTree.node 72 (TableTree.node 65 (TableTree.node 61 (TableTree.node 59 (TableTree.leaf (0)) (TableTree.node 60 (TableTree.leaf (0)) (TableTree.leaf (44)))) (TableTree.node 63 (TableTree.node 62 (TableTree.leaf (44)) (TableTree.leaf (42))) (TableTree.node 64 (TableTree.leaf (44)) (TableTree.leaf (0))))) (TableTree.node 68 (TableTree.node 66 (TableTree.leaf (0)) (TableTree.node 67 (TableTree.leaf (0)) (TableTree.leaf (0)))) (TableTree.node 70 (TableTree.node 69 (TableTree.leaf (0)) (TableTree.leaf (0))) (TableTree.node 71 (TableTree.leaf (0)) (TableTree.leaf (0)))))) (TableTree.node 79 (TableTree.node 75 (TableTree.node 73 (TableTree.leaf (44)) (TableTree.node 74 (TableTree.leaf (44)) (TableTree.leaf (42)))) (TableTree.node 77 (TableTree.node 76 (TableTree.leaf (43)) (TableTree.leaf (0))) (TableTree.node 78 (TableTree.leaf (44)) (TableTree.leaf (0))))) (TableTree.node 83 (TableTree.node 81 (TableTree.node 80 (TableTree.leaf (42)) (TableTree.leaf (20))) (TableTree.node 82 (TableTree.leaf (0)) (TableTree.leaf (38)))) (TableTree.node 85 (TableTree.node 84 (TableTree.leaf (0)) (TableTree.leaf (0))) (TableTree.node 86 (TableTree.leaf (0)) (TableTree.leaf (0))))))) (TableTree.node 101 (TableTree.node 94 (TableTree.node 90 (TableTree.node 88 (TableTree.leaf (0)) (TableTree.node 89 (TableTree.leaf (0)) (TableTree.leaf (42)))) (TableTree.node 92 (TableTree.node 91 (TableTree.leaf (44)) (TableTree.leaf (0))) (TableTree.node 93 (TableTree.leaf (43)) (TableTree.leaf (44))))) (TableTree.node 97 (TableTree.node 95 (TableTree.leaf (44)) (TableTree.node 96 (TableTree.leaf (0)) (TableTree.leaf (0)))) (TableTree.node 99 (TableTree.node 98 (TableTree.leaf (44)) (TableTree.leaf (0))) (TableTree.node 100 (TableTree.leaf (44)) (TableTree.leaf (44)))))) (TableTree.node 108 (TableTree.node 104 (TableTree.node 102 (TableTree.leaf (44)) (TableTree.node 103 (TableTree.leaf (44)) (TableTree.leaf (42)))) (TableTree.node 106 (TableTree.node 105 (TableTree.leaf (43)) (TableTree.leaf (0))) (TableTree.node 107 (TableTree.leaf (0)) (TableTree.leaf (0))))) (TableTree.node 112 (TableTree.node 110 (TableTree.node 109 (TableTree.leaf (0)) (TableTree.leaf (0))) (TableTree.node 111 (TableTree.leaf (0)) (TableTree.leaf (0)))) (TableTree.node 114 (TableTree.node 113 (TableTree.leaf (0)) (TableTree.leaf (0))) (TableTree.node 115 (TableTree.leaf (0)) (TableTree.leaf (0))))))))) (TableTree.node 174 (TableTree.node 145 (TableTree.node 130 (TableTree.node 123 (TableTree.node 119 (TableTree.node 117 (TableTree.leaf (0)) (TableTree.node 118 (TableTree.leaf (44)) (TableTree.leaf (44)))) (TableTree.node 121 (TableTree.node 120 (TableTree.leaf (0)) (TableTree.leaf (44))) (TableTree.node 122 (TableTree.leaf (44)) (TableTree.leaf (0))))) (TableTree.node 126 (TableTree.node 124 (TableTree.leaf (0)) (TableTree.node 125 (TableTree.leaf (0)) (TableTree.leaf (0)))) (TableTree.node 128 (TableTree.node 127 (TableTree.leaf (42)) (TableTree.leaf (44))) (TableTree.node 129 (TableTree.leaf (44)) (TableTree.leaf (44)))))) (TableTree.node 137 (TableTree.node 133 (TableTree.node 131 (TableTree.leaf (0)) (TableTree.node 132 (TableTree.leaf (0)) (TableTree.leaf (44)))) (TableTree.node 135 (TableTree.node 134 (TableTree.leaf (44)) (TableTree.leaf (44))) (TableTree.node 136 (TableTree.leaf (44)) (TableTree.leaf (0))))) (TableTree.node 141 (TableTree.node 139 (TableTree.node 138 (TableTree.leaf (0)) (TableTree.leaf (0))) (TableTree.node 140 (TableTree.leaf (0)) (TableTree.leaf (0)))) (TableTree.node 143 (TableTree.node 142 (TableTree.leaf (0)) (TableTree.leaf (0))) (TableTree.node 144 (TableTree.leaf (0)) (TableTree.leaf (42))))))) (TableTree.node 159 (TableTree.node 152 (TableTree.node 148 (TableTree.node 146 (TableTree.leaf (43)) (TableTree.node 147 (TableTree.leaf (44)) (TableTree.leaf (44)))) (TableTree.node 150 (TableTree.node 149 (TableTree.leaf (0)) (TableTree.leaf (42))) (TableTree.node 151 (TableTree.leaf (0)) (TableTree.leaf (44))))) (TableTree.node 155 (TableTree.node 153 (TableTree.leaf (43)) (TableTree.node 154 (TableTree.leaf (0)) (TableTree.leaf (44)))) (TableTree.node 157 (TableTree.node 156 (TableTree.leaf (0)) (TableTree.leaf (0))) (TableTree.node 158 (TableTree.leaf (0)) (TableTree.leaf (0)))))) (TableTree.node 166 (TableTree.node 162 (TableTree.node 160 (TableTree.leaf (0)) (TableTree.node 161 (TableTree.leaf (0)) (TableTree.leaf (43)))) (TableTree.node 164 (TableTree.node 163 (TableTree.leaf (0)) (TableTree.leaf (42))) (TableTree.node 165 (TableTree.leaf (44)) (TableTree.leaf (44))))) (TableTree.node 170 (TableTree.node 168 (TableTree.node 167 (TableTree.leaf (0)) (TableTree.leaf (44))) (TableTree.node 169 (TableTree.leaf (44)) (TableTree.leaf (0)))) (TableTree.node 172 (TableTree.node 171 (TableTree.leaf (0)) (TableTree.leaf (42))) (TableTree.node 173 (TableTree.leaf (43)) (TableTree.leaf (44)))))))) (TableTree.node 203 (TableTree.node 188 (TableTree.node 181 (TableTree.node 177 (TableTree.node 175 (TableTree.leaf (44)) (TableTree.node 176 (TableTree.leaf (44)) (TableTree.leaf (44)))) (TableTree.node 179 (TableTree.node 178 (TableTree.leaf (0)) (TableTree.leaf (0))) (TableTree.node 180 (TableTree.leaf (0)) (TableTree.leaf (0))))) (TableTree.node 184 (TableTree.node 182 (TableTree.leaf (0)) (TableTree.node 183 (TableTree.leaf (0)) (TableTree.leaf (0)))) (TableTree.node 186 (TableTree.node 185 (TableTree.leaf (0)) (TableTree.leaf (0))) (TableTree.node 187 (TableTree.leaf (0)) (TableTree.leaf (0)))))) (TableTree.node 195 (TableTree.node 191 (TableTree.node 189 (TableTree.leaf (0)) (TableTree.node 190 (TableTree.leaf (44)) (TableTree.leaf (44)))) (TableTree.node 193 (TableTree.node 192 (TableTree.leaf (0)) (TableTree.leaf (44))) (TableTree.node 194 (TableTree.leaf (42)) (TableTree.leaf (43))))) (TableTree.node 199 (TableTree.node 197 (TableTree.node 196 (TableTree.leaf (0)) (TableTree.leaf (41))) (TableTree.node 198 (TableTree.leaf (44)) (TableTree.leaf (0)))) (TableTree.node 201 (TableTree.node 200 (TableTree.leaf (0)) (TableTree.leaf (0))) (TableTree.node 202 (TableTree.leaf (44)) (TableTree.leaf (0))))))) (TableTree.node 217 (TableTree.node 210 (TableTree.node 206 (TableTree.node 204 (TableTree.leaf (0)) (TableTree.node 205 (TableTree.leaf (0)) (TableTree.leaf (0)))) (TableTree.node 208 (TableTree.node 207 (TableTree.leaf (42)) (TableTree.leaf (44))) (TableTree.node 209 (TableTree.leaf (44)) (TableTree.leaf (44))))) (TableTree.node 213 (TableTree.node 211 (TableTree.leaf (0)) (TableTree.node 212 (TableTree.leaf (0)) (TableTree.leaf (0)))) (TableTree.node 215 (TableTree.node 214 (TableTree.leaf (41)) (TableTree.leaf (68))) (TableTree.node 216 (TableTree.leaf (0)) (TableTree.leaf (44)))))) (TableTree.node 224 (TableTree.node 220 (TableTree.node 218 (TableTree.leaf (44)) (TableTree.node 219 (TableTree.leaf (44)) (TableTree.leaf (44)))) (TableTree.node 222 (TableTree.node 221 (TableTree.leaf (0)) (TableTree.leaf (0))) (TableTree.node 223 (TableTree.leaf (0)) (TableTree.leaf (0))))) (TableTree.node 228 (TableTree.node 226 (TableTree.node 225 (TableTree.leaf (44)) (TableTree.leaf (44))) (TableTree.node 227 (TableTree.leaf (0)) (TableTree.leaf (0)))) (TableTree.node 230 (TableTree.node 229 (TableTree.leaf (0)) (TableTree.leaf (0))) (TableTree.node 231 (TableTree.leaf (0)) (TableTree.leaf (0)))))))))) (TableTree.node 348 (TableTree.node 290 (TableTree.node 261 (TableTree.node 246 (TableTree.node 239 (TableTree.node 235 (TableTree.node 233 (TableTree.leaf (42)) (TableTree.node 234 (TableTree.leaf (42)) (TableTree.leaf (43)))) (TableTree.node 237 (TableTree.node 236 (TableTree.leaf (43)) (TableTree.leaf (44))) (TableTree.node 238 (TableTree.leaf (44)) (TableTree.leaf (0))))) (TableTree.node 242 (TableTree.node 240 (TableTree.leaf (0)) (TableTree.node 241 (TableTree.leaf (68)) (TableTree.leaf (41)))) (TableTree.node 244 (TableTree.node 243 (TableTree.leaf (0)) (TableTree.leaf (0))) (TableTree.node 245 (TableTree.leaf (42)) (TableTree.leaf (42)))))) (TableTree.node 253 (TableTree.node 249 (TableTree.node 247 (TableTree.leaf (0)) (TableTree.node 248 (TableTree.leaf (44)) (TableTree.leaf (44)))) (TableTree.node 251 (TableTree.node 250 (TableTree.leaf (44)) (TableTree.leaf (0))) (TableTree.node 252 (TableTree.leaf (0)) (TableTree.leaf (44))))) (TableTree.node 257 (TableTree.node 255 (TableTree.node 254 (TableTree.leaf (0)) (TableTree.leaf (0))) (TableTree.node 256 (TableTree.leaf (42)) (TableTree.leaf (43)))) (TableTree.node 259 (TableTree.node 258 (TableTree.leaf (0)) (TableTree.leaf (0))) (TableTree.node 260 (TableTree.leaf (0)) (TableTree.leaf (0))))))) (TableTree.node 275 (TableTree.node 268 (TableTree.node 264 (TableTree.node 262 (TableTree.leaf (0)) (TableTree.node 263 (TableTree.leaf (0)) (TableTree.leaf (0)))) (TableTree.node 266 (TableTree.node 265 (TableTree.leaf (0)) (TableTree.leaf (0))) (TableTree.node 267 (TableTree.leaf (42)) (TableTree.leaf (0))))) (TableTree.node 271 (TableTree.node 269 (TableTree.leaf (42)) (TableTree.node 270 (TableTree.leaf (44)) (TableTree.leaf (0)))) (TableTree.node 273 (TableTree.node 272 (TableTree.leaf (0)) (TableTree.leaf (0))) (TableTree.node 274 (TableTree.leaf (41)) (TableTree.leaf (44)))))) (TableTree.node 282 (TableTree.node 278 (TableTree.node 276 (TableTree.leaf (0)) (TableTree.node 277 (TableTree.leaf (44)) (TableTree.leaf (44)))) (TableTree.node 280 (TableTree.node 279 (TableTree.leaf (0)) (TableTree.leaf (0))) (TableTree.node 281 (TableTree.leaf (42)) (TableTree.leaf (43))))) (TableTree.node 286 (TableTree.node 284 (TableTree.node 283 (TableTree.leaf (44)) (TableTree.leaf (44))) (TableTree.node 285 (TableTree.leaf (44)) (TableTree.leaf (44)))) (TableTree.node 288 (TableTree.node 287 (TableTree.leaf (44)) (TableTree.leaf (0))) (TableTree.node 289 (TableTree.leaf (42)) (TableTree.leaf (43)))))))) (TableTree.node 319 (TableTree.node 304 (TableTree.node 297 (TableTree.node 293 (TableTree.node 291 (TableTree.leaf (0)) (TableTree.node 292 (TableTree.leaf (0)) (TableTree.leaf (0)))) (TableTree.node 295 (TableTree.node 294 (TableTree.leaf (0)) (TableTree.leaf (0))) (TableTree.node 296 (TableTree.leaf (0)) (TableTree.leaf (0))))) (TableTree.node 300 (TableTree.node 298 (TableTree.leaf (0)) (TableTree.node 299 (TableTree.leaf (0)) (TableTree.leaf (0)))) (TableTree.node 302 (TableTree.node 301 (TableTree.leaf (0)) (TableTree.leaf (0))) (TableTree.node 303 (TableTree.leaf (0)) (TableTree.leaf (0)))))) (TableTree.node 311 (TableTree.node 307 (TableTree.node 305 (TableTree.leaf (0)) (TableTree.node 306 (TableTree.leaf (0)) (TableTree.leaf (42)))) (TableTree.node 309 (TableTree.node 308 (TableTree.leaf (44)) (TableTree.leaf (44))) (TableTree.node 310 (TableTree.leaf (44)) (TableTree.leaf (0))))) (TableTree.node 315 (TableTree.node 313 (TableTree.node 312 (TableTree.leaf (0)) (TableTree.leaf (44))) (TableTree.node 314 (TableTree.leaf (44)) (TableTree.leaf (44)))) (TableTree.node 317 (TableTree.node 316 (TableTree.leaf (44)) (TableTree.leaf (0))) (TableTree.node 318 (TableTree.leaf (0)) (TableTree.leaf (0))))))) (TableTree.node 333 (TableTree.node 326 (TableTree.node 322 (TableTree.node 320 (TableTree.leaf (0)) (TableTree.node 321 (TableTree.leaf (0)) (TableTree.leaf (0)))) (TableTree.node 324 (TableTree.node 323 (TableTree.leaf (0)) (TableTree.leaf (0))) (TableTree.node 325 (TableTree.leaf (42)) (TableTree.leaf (42))))) (TableTree.node 329 (TableTree.node 327 (TableTree.leaf (43)) (TableTree.node 328 (TableTree.leaf (43)) (TableTree.leaf (44)))) (TableTree.node 331 (TableTree.node 330 (TableTree.leaf (44)) (TableTree.leaf (0))) (TableTree.node 332 (TableTree.leaf (0)) (TableTree.leaf (42)))))) (TableTree.node 340 (TableTree.node 336 (TableTree.node 334 (TableTree.leaf (42)) (TableTree.node 335 (TableTree.leaf (0)) (TableTree.leaf (44)))) (TableTree.node 338 (TableTree.node 337 (TableTree.leaf (44)) (TableTree.leaf (44))) (TableTree.node 339 (TableTree.leaf (0)) (TableTree.leaf (0))))) (TableTree.node 344 (TableTree.node 342 (TableTree.node 341 (TableTree.leaf (44)) (TableTree.leaf (0))) (TableTree.node 343 (TableTree.leaf (0)) (TableTree.leaf (0)))) (TableTree.node 346 (TableTree.node 345 (TableTree.leaf (0)) (TableTree.leaf (0))) (TableTree.node 347 (TableTree.leaf (0)) (TableTree.leaf (0))))))))) (TableTree.node 406 (TableTree.node 377 (TableTree.node 362 (TableTree.node 355 (TableTree.node 351 (TableTree.node 349 (TableTree.leaf (0)) (TableTree.node 350 (TableTree.leaf (0)) (TableTree.leaf (42)))) (TableTree.node 353 (TableTree.node 352 (TableTree.leaf (0)) (TableTree.leaf (44))) (TableTree.node 354 (TableTree.leaf (0)) (TableTree.leaf (42))))) (TableTree.node 358 (TableTree.node 356 (TableTree.leaf (43)) (TableTree.node 357 (TableTree.leaf (0)) (TableTree.leaf (0)))) (TableTree.node 360 (TableTree.node 359 (TableTree.leaf (0)) (TableTree.leaf (0))) (TableTree.node 361 (TableTree.leaf (42)) (TableTree.leaf (43)))))) (TableTree.node 369 (TableTree.node 365 (TableTree.node 363 (TableTree.leaf (0)) (TableTree.node 364 (TableTree.leaf (41)) (TableTree.leaf (44)))) (TableTree.node 367 (TableTree.node 366 (TableTree.leaf (0)) (TableTree.leaf (0))) (TableTree.node 368 (TableTree.leaf (0)) (TableTree.leaf (0))))) (TableTree.node 373 (TableTree.node 371 (TableTree.node 370 (TableTree.leaf (41)) (TableTree.leaf (68))) (TableTree.node 372 (TableTree.leaf (0)) (TableTree.leaf (44)))) (TableTree.node 375 (TableTree.node 374 (TableTree.leaf (0)) (TableTree.leaf (0))) (TableTree.node 376 (TableTree.leaf (68)) (TableTree.leaf (41))))))) (TableTree.node 391 (TableTree.node 384 (TableTree.node 380 (TableTree.node 378 (TableTree.leaf (42)) (TableTree.node 379 (TableTree.leaf (42)) (TableTree.leaf (43)))) (TableTree.node 382 (TableTree.node 381 (TableTree.leaf (43)) (TableTree.leaf (44))) (TableTree.node 383 (TableTree.leaf (44)) (TableTree.leaf (0))))) (TableTree.node 387 (TableTree.node 385 (TableTree.leaf (42)) (TableTree.node 386 (TableTree.leaf (43)) (TableTree.leaf (0)))) (TableTree.node 389 (TableTree.node 388 (TableTree.leaf (0)) (TableTree.leaf (0))) (TableTree.node 390 (TableTree.leaf (42)) (TableTree.leaf (42)))))) (TableTree.node 398 (TableTree.node 394 (TableTree.node 392 (TableTree.leaf (0)) (TableTree.node 393 (TableTree.leaf (44)) (TableTree.leaf (44)))) (TableTree.node 396 (TableTree.node 395 (TableTree.leaf (44)) (TableTree.leaf (0))) (TableTree.node 397 (TableTree.leaf (0)) (TableTree.leaf (44))))) (TableTree.node 402 (TableTree.node 400 (TableTree.node 399 (TableTree.leaf (0)) (TableTree.leaf (0))) (TableTree.node 401 (TableTree.leaf (0)) (TableTree.leaf (0)))) (TableTree.node 404 (TableTree.node 403 (TableTree.leaf (41)) (TableTree.leaf (0))) (TableTree.node 405 (TableTree.leaf (0)) (TableTree.leaf (0)))))))) (TableTree.node 435 (TableTree.node 420 (TableTree.node 413 (TableTree.node 409 (TableTree.node 407 (TableTree.leaf (0)) (TableTree.node 408 (TableTree.leaf (0)) (TableTree.leaf (0)))) (TableTree.node 411 (TableTree.node 410 (TableTree.leaf (0)) (TableTree.leaf (0))) (TableTree.node 412 (TableTree.leaf (0)) (TableTree.leaf (44))))) (TableTree.node 416 (TableTree.node 414 (TableTree.leaf (0)) (TableTree.node 415 (TableTree.leaf (44)) (TableTree.leaf (0)))) (TableTree.node 418 (TableTree.node 417 (TableTree.leaf (44)) (TableTree.leaf (43))) (TableTree.node 419 (TableTree.leaf (44)) (TableTree.leaf (0)))))) (TableTree.node 427 (TableTree.node 423 (TableTree.node 421 (TableTree.leaf (0)) (TableTree.node 422 (TableTree.leaf (0)) (TableTree.leaf (0)))) (TableTree.node 425 (TableTree.node 424 (TableTree.leaf (0)) (TableTree.leaf (0))) (TableTree.node 426 (TableTree.leaf (0)) (TableTree.leaf (0))))) (TableTree.node 431 (TableTree.node 429 (TableTree.node 428 (TableTree.leaf (0)) (TableTree.leaf (0))) (TableTree.node 430 (TableTree.leaf (42)) (TableTree.leaf (43)))) (TableTree.node 433 (TableTree.node 432 (TableTree.leaf (0)) (TableTree.leaf (41))) (TableTree.node 434 (TableTree.leaf (41)) (TableTree.leaf (0))))))) (TableTree.node 449 (TableTree.node 442 (TableTree.node 438 (TableTree.node 436 (TableTree.leaf (0)) (TableTree.node 437 (TableTree.leaf (0)) (TableTree.leaf (0)))) (TableTree.node 440 (TableTree.node 439 (TableTree.leaf (0)) (TableTree.leaf (42))) (TableTree.node 441 (TableTree.leaf (42)) (TableTree.leaf (44))))) (TableTree.node 445 (TableTree.node 443 (TableTree.leaf (44)) (TableTree.node 444 (TableTree.leaf (0)) (TableTree.leaf (44)))) (TableTree.node 447 (TableTree.node 446 (TableTree.leaf (44)) (TableTree.leaf (0))) (TableTree.node 448 (TableTree.leaf (0)) (TableTree.leaf (42)))))) (TableTree.node 456 (TableTree.node 452 (TableTree.node 450 (TableTree.leaf (43)) (TableTree.node 451 (TableTree.leaf (44)) (TableTree.leaf (44)))) (TableTree.node 454 (TableTree.node 453 (TableTree.leaf (44)) (TableTree.leaf (44))) (TableTree.node 455 (TableTree.leaf (0)) (TableTree.leaf (0))))) (TableTree.node 460 (TableTree.node 458 (TableTree.node 457 (TableTree.leaf (42)) (TableTree.leaf (44))) (TableTree.node 459 (TableTree.leaf (0)) (TableTree.leaf (42)))) (TableTree.node 462 (TableTree.node 461 (TableTree.leaf (43)) (TableTree.leaf (0))) (TableTree.node 463 (TableTree.leaf (0)) (TableTree.leaf (0))))))))))) (TableTree.node 696 (TableTree.node 580 (TableTree.node 522 (TableTree.node 493 (TableTree.node 478 (TableTree.node 471 (TableTree.node 467 (TableTree.node 465 (TableTree.leaf (0)) (TableTree.node 466 (TableTree.leaf (0)) (TableTree.leaf (0)))) (TableTree.node 469 (TableTree.node 468 (TableTree.leaf (0)) (TableTree.leaf (0))) (TableTree.node 470 (TableTree.leaf (0)) (TableTree.leaf (0))))) (TableTree.node 474 (TableTree.node 472 (TableTree.leaf (0)) (TableTree.node 473 (TableTree.leaf (0)) (TableTree.leaf (42)))) (TableTree.node 476 (TableTree.node 475 (TableTree.leaf (42)) (TableTree.leaf (43))) (TableTree.node 477 (TableTree.leaf (43)) (TableTree.leaf (42)))))) (TableTree.node 485 (TableTree.node 481 (TableTree.node 479 (TableTree.leaf (43)) (TableTree.node 480 (TableTree.leaf (0)) (TableTree.leaf (0)))) (TableTree.node 483 (TableTree.node 482 (TableTree.leaf (41)) (TableTree.leaf (41))) (TableTree.node 484 (TableTree.leaf (0)) (TableTree.leaf (41))))) (TableTree.node 489 (TableTree.node 487 (TableTree.node 486 (TableTree.leaf (44)) (TableTree.leaf (44))) (TableTree.node 488 (TableTree.leaf (0)) (TableTree.leaf (44)))) (TableTree.node 491 (TableTree.node 490 (TableTree.leaf (0)) (TableTree.leaf (0))) (TableTree.node 492 (TableTree.leaf (0)) (TableTree.leaf (0))))))) (TableTree.node 507 (TableTree.node 500 (TableTree.node 496 (TableTree.node 494 (TableTree.leaf (41)) (TableTree.node 495 (TableTree.leaf (41)) (TableTree.leaf (0)))) (TableTree.node 498 (TableTree.node 497 (TableTree.leaf (41)) (TableTree.leaf (44))) (TableTree.node 499 (TableTree.leaf (44)) (TableTree.leaf (0))))) (TableTree.node 503 (TableTree.node 501 (TableTree.leaf (0)) (TableTree.node 502 (TableTree.leaf (44)) (TableTree.leaf (0)))) (TableTree.node 505 (TableTree.node 504 (TableTree.leaf (0)) (TableTree.leaf (0))) (TableTree.node 506 (TableTree.leaf (0)) (TableTree.leaf (0)))))) (TableTree.node 514 (TableTree.node 510 (TableTree.node 508 (TableTree.leaf (0)) (TableTree.node 509 (TableTree.leaf (0)) (TableTree.leaf (44)))) (TableTree.node 512 (TableTree.node 511 (TableTree.leaf (0)) (TableTree.leaf (0))) (TableTree.node 513 (TableTree.leaf (0)) (TableTree.leaf (0))))) (TableTree.node 518 (TableTree.node 516 (TableTree.node 515 (TableTree.leaf (0)) (TableTree.leaf (42))) (TableTree.node 517 (TableTree.leaf (0)) (TableTree.leaf (42)))) (TableTree.node 520 (TableTree.node 519 (TableTree.leaf (0)) (TableTree.leaf (42))) (TableTree.node 521 (TableTree.leaf (0)) (TableTree.leaf (0)))))))) (TableTree.node 551 (TableTree.node 536 (TableTree.node 529 (TableTree.node 525 (TableTree.node 523 (TableTree.leaf (44)) (TableTree.node 524 (TableTree.leaf (0)) (TableTree.leaf (0)))) (TableTree.node 527 (TableTree.node 526 (TableTree.leaf (0)) (TableTree.leaf (0))) (TableTree.node 528 (TableTree.leaf (44)) (TableTree.leaf (42))))) (TableTree.node 532 (TableTree.node 530 (TableTree.leaf (0)) (TableTree.node 531 (TableTree.leaf (0)) (TableTree.leaf (0)))) (TableTree.node 534 (TableTree.node 533 (TableTree.leaf (0)) (TableTree.leaf (0))) (TableTree.node 535 (TableTree.leaf (0)) (TableTree.leaf (0)))))) (TableTree.node 543 (TableTree.node 539 (TableTree.node 537 (TableTree.leaf (42)) (TableTree.node 538 (TableTree.leaf (43)) (TableTree.leaf (42)))) (TableTree.node 541 (TableTree.node 540 (TableTree.leaf (42)) (TableTree.leaf (43))) (TableTree.node 542 (TableTree.leaf (43)) (TableTree.leaf (44))))) (TableTree.node 547 (TableTree.node 545 (TableTree.node 544 (TableTree.leaf (44)) (TableTree.leaf (42))) (TableTree.node 546 (TableTree.leaf (43)) (TableTree.leaf (0)))) (TableTree.node 549 (TableTree.node 548 (TableTree.leaf (0)) (TableTree.leaf (0))) (TableTree.node 550 (TableTree.leaf (0)) (TableTree.leaf (41))))))) (TableTree.node 565 (TableTree.node 558 (TableTree.node 554 (TableTree.node 552 (TableTree.leaf (41)) (TableTree.node 553 (TableTree.leaf (0)) (TableTree.leaf (42)))) (TableTree.node 556 (TableTree.node 555 (TableTree.leaf (43)) (TableTree.leaf (0))) (TableTree.node 557 (TableTree.leaf (0)) (TableTree.leaf (0))))) (TableTree.node 561 (TableTree.node 559 (TableTree.leaf (42)) (TableTree.node 560 (TableTree.leaf (42)) (TableTree.leaf (0)))) (TableTree.node 563 (TableTree.node 562 (TableTree.leaf (44)) (TableTree.leaf (44))) (TableTree.node 564 (TableTree.leaf (44)) (TableTree.leaf (0)))))) (TableTree.node 572 (TableTree.node 568 (TableTree.node 566 (TableTree.leaf (0)) (TableTree.node 567 (TableTree.leaf (44)) (TableTree.leaf (0)))) (TableTree.node 570 (TableTree.node 569 (TableTree.leaf (0)) (TableTree.leaf (0))) (TableTree.node 571 (TableTree.leaf (0)) (TableTree.leaf (41))))) (TableTree.node 576 (TableTree.node 574 (TableTree.node 573 (TableTree.leaf (0)) (TableTree.leaf (0))) (TableTree.node 575 (TableTree.leaf (0)) (TableTree.leaf (0)))) (TableTree.node 578 (TableTree.node 577 (TableTree.leaf (0)) (TableTree.leaf (0))) (TableTree.node 579 (TableTree.leaf (0)) (TableTree.leaf (0))))))))) (TableTree.node 638 (TableTree.node 609 (TableTree.node 594 (TableTree.node 587 (TableTree.node 583 (TableTree.node 581 (TableTree.leaf (42)) (TableTree.node 582 (TableTree.leaf (0)) (TableTree.leaf (42)))) (TableTree.node 585 (TableTree.node 584 (TableTree.leaf (44)) (TableTree.leaf (0))) (TableTree.node 586 (TableTree.leaf (42)) (TableTree.leaf (43))))) (TableTree.node 590 (TableTree.node 588 (TableTree.leaf (0)) (TableTree.node 589 (TableTree.leaf (0)) (TableTree.leaf (0)))) (TableTree.node 592 (TableTree.node 591 (TableTree.leaf (0)) (TableTree.leaf (44))) (TableTree.node 593 (TableTree.leaf (0)) (TableTree.leaf (42)))))) (TableTree.node 601 (TableTree.node 597 (TableTree.node 595 (TableTree.leaf (43)) (TableTree.node 596 (TableTree.leaf (44)) (TableTree.leaf (0)))) (TableTree.node 599 (TableTree.node 598 (TableTree.leaf (44)) (TableTree.leaf (44))) (TableTree.node 600 (TableTree.leaf (0)) (TableTree.leaf (0))))) (TableTree.node 605 (TableTree.node 603 (TableTree.node 602 (TableTree.leaf (42)) (TableTree.leaf (43))) (TableTree.node 604 (TableTree.leaf (44)) (TableTree.leaf (44)))) (TableTree.node 607 (TableTree.node 606 (TableTree.leaf (44)) (TableTree.leaf (44))) (TableTree.node 608 (TableTree.leaf (0)) (TableTree.leaf (0))))))) (TableTree.node 623 (TableTree.node 616 (TableTree.node 612 (TableTree.node 610 (TableTree.leaf (0)) (TableTree.node 611 (TableTree.leaf (0)) (TableTree.leaf (0)))) (TableTree.node 614 (TableTree.node 613 (TableTree.leaf (0)) (TableTree.leaf (0))) (TableTree.node 615 (TableTree.leaf (0)) (TableTree.leaf (0))))) (TableTree.node 619 (TableTree.node 617 (TableTree.leaf (0)) (TableTree.node 618 (TableTree.leaf (0)) (TableTree.leaf (0)))) (TableTree.node 621 (TableTree.node 620 (TableTree.leaf (0)) (TableTree.leaf (0))) (TableTree.node 622 (TableTree.leaf (0)) (TableTree.leaf (0)))))) (TableTree.node 630 (TableTree.node 626 (TableTree.node 624 (TableTree.leaf (41)) (TableTree.node 625 (TableTree.leaf (0)) (TableTree.leaf (41)))) (TableTree.node 628 (TableTree.node 627 (TableTree.leaf (41)) (TableTree.leaf (0))) (TableTree.node 629 (TableTree.leaf (0)) (TableTree.leaf (0))))) (TableTree.node 634 (TableTree.node 632 (TableTree.node 631 (TableTree.leaf (0)) (TableTree.leaf (43))) (TableTree.node 633 (TableTree.leaf (43)) (TableTree.leaf (0)))) (TableTree.node 636 (TableTree.node 635 (TableTree.leaf (42)) (TableTree.leaf (44))) (TableTree.node 637 (TableTree.leaf (0)) (TableTree.leaf (0)))))))) (TableTree.node 667 (TableTree.node 652 (TableTree.node 645 (TableTree.node 641 (TableTree.node 639 (TableTree.leaf (0)) (TableTree.node 640 (TableTree.leaf (0)) (TableTree.leaf (0)))) (TableTree.node 643 (TableTree.node 642 (TableTree.leaf (0)) (TableTree.leaf (42))) (TableTree.node 644 (TableTree.leaf (42)) (TableTree.leaf (43))))) (TableTree.node 648 (TableTree.node 646 (TableTree.leaf (43)) (TableTree.node 647 (TableTree.leaf (42)) (TableTree.leaf (43)))) (TableTree.node 650 (TableTree.node 649 (TableTree.leaf (0)) (TableTree.leaf (0))) (TableTree.node 651 (TableTree.leaf (41)) (TableTree.leaf (41)))))) (TableTree.node 659 (TableTree.node 655 (TableTree.node 653 (TableTree.leaf (0)) (TableTree.node 654 (TableTree.leaf (41)) (TableTree.leaf (44)))) (TableTree.node 657 (TableTree.node 656 (TableTree.leaf (44)) (TableTree.leaf (0))) (TableTree.node 658 (TableTree.leaf (44)) (TableTree.leaf (44))))) (TableTree.node 663 (TableTree.node 661 (TableTree.node 660 (TableTree.leaf (44)) (TableTree.leaf (0))) (TableTree.node 662 (TableTree.leaf (0)) (TableTree.leaf (44)))) (TableTree.node 665 (TableTree.node 664 (TableTree.leaf (0)) (TableTree.leaf (0))) (TableTree.node 666 (TableTree.leaf (0)) (TableTree.leaf (0))))))) (TableTree.node 681 (TableTree.node 674 (TableTree.node 670 (TableTree.node 668 (TableTree.leaf (0)) (TableTree.node 669 (TableTree.leaf (0)) (TableTree.leaf (0)))) (TableTree.node 672 (TableTree.node 671 (TableTree.leaf (44)) (TableTree.leaf (0))) (TableTree.node 673 (TableTree.leaf (0)) (TableTree.leaf (0))))) (TableTree.node 677 (TableTree.node 675 (TableTree.leaf (0)) (TableTree.node 676 (TableTree.leaf (0)) (TableTree.leaf (42)))) (TableTree.node 679 (TableTree.node 678 (TableTree.leaf (0)) (TableTree.leaf (42))) (TableTree.node 680 (TableTree.leaf (0)) (TableTree.leaf (42)))))) (TableTree.node 688 (TableTree.node 684 (TableTree.node 682 (TableTree.leaf (0)) (TableTree.node 683 (TableTree.leaf (0)) (TableTree.leaf (42)))) (TableTree.node 686 (TableTree.node 685 (TableTree.leaf (44)) (TableTree.leaf (0))) (TableTree.node 687 (TableTree.leaf (44)) (TableTree.leaf (42))))) (TableTree.node 692 (TableTree.node 690 (TableTree.node 689 (TableTree.leaf (44)) (TableTree.leaf (0))) (TableTree.node 691 (TableTree.leaf (0)) (TableTree.leaf (0)))) (TableTree.node 694 (TableTree.node 693 (TableTree.leaf (44)) (TableTree.leaf (44))) (TableTree.node 695 (TableTree.leaf (0)) (TableTree.leaf (0)))))))))) (TableTree.node 812 (TableTree.node 754 (TableTree.node 725 (TableTree.node 710 (TableTree.node 703 (TableTree.node 699 (TableTree.node 697 (TableTree.leaf (0)) (TableTree.node 698 (TableTree.leaf (0)) (TableTree.leaf (0)))) (TableTree.node 701 (TableTree.node 700 (TableTree.leaf (0)) (TableTree.leaf (42))) (TableTree.node 702 (TableTree.leaf (43)) (TableTree.leaf (0))))) (TableTree.node 706 (TableTree.node 704 (TableTree.leaf (0)) (TableTree.node 705 (TableTree.leaf (0)) (TableTree.leaf (42)))) (TableTree.node 708 (TableTree.node 707 (TableTree.leaf (43)) (TableTree.leaf (0))) (TableTree.node 709 (TableTree.leaf (0)) (TableTree.leaf (0)))))) (TableTree.node 717 (TableTree.node 713 (TableTree.node 711 (TableTree.leaf (0)) (TableTree.node 712 (TableTree.leaf (0)) (TableTree.leaf (0)))) (TableTree.node 715 (TableTree.node 714 (TableTree.leaf (42)) (TableTree.leaf (43))) (TableTree.node 716 (TableTree.leaf (0)) (TableTree.leaf (41))))) (TableTree.node 721 (TableTree.node 719 (TableTree.node 718 (TableTree.leaf (41)) (TableTree.leaf (0))) (TableTree.node 720 (TableTree.leaf (0)) (TableTree.leaf (0)))) (TableTree.node 723 (TableTree.node 722 (TableTree.leaf (0)) (TableTree.leaf (41))) (TableTree.node 724 (TableTree.leaf (41)) (TableTree.leaf (0))))))) (TableTree.node 739 (TableTree.node 732 (TableTree.node 728 (TableTree.node 726 (TableTree.leaf (0)) (TableTree.node 727 (TableTree.leaf (0)) (TableTree.leaf (0)))) (TableTree.node 730 (TableTree.node 729 (TableTree.leaf (0)) (TableTree.leaf (41))) (TableTree.node 731 (TableTree.leaf (41)) (TableTree.leaf (0))))) (TableTree.node 735 (TableTree.node 733 (TableTree.leaf (41)) (TableTree.node 734 (TableTree.leaf (44)) (TableTree.leaf (0)))) (TableTree.node 737 (TableTree.node 736 (TableTree.leaf (68)) (TableTree.leaf (44))) (TableTree.node 738 (TableTree.leaf (0)) (TableTree.leaf (0)))))) (TableTree.node 746 (TableTree.node 742 (TableTree.node 740 (TableTree.leaf (0)) (TableTree.node 741 (TableTree.leaf (0)) (TableTree.leaf (42)))) (TableTree.node 744 (TableTree.node 743 (TableTree.leaf (0)) (TableTree.leaf (42))) (TableTree.node 745 (TableTree.leaf (44)) (TableTree.leaf (42))))) (TableTree.node 750 (TableTree.node 748 (TableTree.node 747 (TableTree.leaf (44)) (TableTree.leaf (0))) (TableTree.node 749 (TableTree.leaf (0)) (TableTree.leaf (68)))) (TableTree.node 752 (TableTree.node 751 (TableTree.leaf (42)) (TableTree.leaf (43))) (TableTree.node 753 (TableTree.leaf (0)) (TableTree.leaf (0)))))))) (TableTree.node 783 (TableTree.node 768 (TableTree.node 761 (TableTree.node 757 (TableTree.node 755 (TableTree.leaf (41)) (TableTree.node 756 (TableTree.leaf (41)) (TableTree.leaf (0)))) (TableTree.node 759 (TableTree.node 758 (TableTree.leaf (41)) (TableTree.leaf (41))) (TableTree.node 760 (TableTree.leaf (41)) (TableTree.leaf (0))))) (TableTree.node 764 (TableTree.node 762 (TableTree.leaf (0)) (TableTree.node 763 (TableTree.leaf (41)) (TableTree.leaf (0)))) (TableTree.node 766 (TableTree.node 765 (TableTree.leaf (0)) (TableTree.leaf (0))) (TableTree.node 767 (TableTree.leaf (0)) (TableTree.leaf (0)))))) (TableTree.node 775 (TableTree.node 771 (TableTree.node 769 (TableTree.leaf (0)) (TableTree.node 770 (TableTree.leaf (0)) (TableTree.leaf (0)))) (TableTree.node 773 (TableTree.node 772 (TableTree.leaf (0)) (TableTree.leaf (0))) (TableTree.node 774 (TableTree.leaf (0)) (TableTree.leaf (43))))) (TableTree.node 779 (TableTree.node 777 (TableTree.node 776 (TableTree.leaf (68)) (TableTree.leaf (43))) (TableTree.node 778 (TableTree.leaf (68)) (TableTree.leaf (0)))) (TableTree.node 781 (TableTree.node 780 (TableTree.leaf (0)) (TableTree.leaf (0))) (TableTree.node 782 (TableTree.leaf (43)) (TableTree.leaf (68))))))) (TableTree.node 797 (TableTree.node 790 (TableTree.node 786 (TableTree.node 784 (TableTree.leaf (0)) (TableTree.node 785 (TableTree.leaf (41)) (TableTree.leaf (41)))) (TableTree.node 788 (TableTree.node 787 (TableTree.leaf (0)) (TableTree.leaf (0))) (TableTree.node 789 (TableTree.leaf (41)) (TableTree.leaf (0))))) (TableTree.node 793 (TableTree.node 791 (TableTree.leaf (0)) (TableTree.node 792 (TableTree.leaf (0)) (TableTree.leaf (0)))) (TableTree.node 795 (TableTree.node 794 (TableTree.leaf (0)) (TableTree.leaf (0))) (TableTree.node 796 (TableTree.leaf (0)) (TableTree.leaf (43)))))) (TableTree.node 804 (TableTree.node 800 (TableTree.node 798 (TableTree.leaf (68)) (TableTree.node 799 (TableTree.leaf (43)) (TableTree.leaf (0)))) (TableTree.node 802 (TableTree.node 801 (TableTree.leaf (0)) (TableTree.leaf (0))) (TableTree.node 803 (TableTree.leaf (0)) (TableTree.leaf (0))))) (TableTree.node 808 (TableTree.node 806 (TableTree.node 805 (TableTree.leaf (41)) (TableTree.leaf (0))) (TableTree.node 807 (TableTree.leaf (41)) (TableTree.leaf (0)))) (TableTree.node 810 (TableTree.node 809 (TableTree.leaf (0)) (TableTree.leaf (41))) (TableTree.node 811 (TableTree.leaf (41)) (TableTree.leaf (0))))))))) (TableTree.node 870 (TableTree.node 841 (TableTree.node 826 (TableTree.node 819 (TableTree.node 815 (TableTree.node 813 (TableTree.leaf (0)) (TableTree.node 814 (TableTree.leaf (0)) (TableTree.leaf (0)))) (TableTree.node 817 (TableTree.node 816 (TableTree.leaf (0)) (TableTree.leaf (0))) (TableTree.node 818 (TableTree.leaf (0)) (TableTree.leaf (0))))) (TableTree.node 822 (TableTree.node 820 (TableTree.leaf (0)) (TableTree.node 821 (TableTree.leaf (0)) (TableTree.leaf (42)))) (TableTree.node 824 (TableTree.node 823 (TableTree.leaf (42)) (TableTree.leaf (44))) (TableTree.node 825 (TableTree.leaf (44)) (TableTree.leaf (0)))))) (TableTree.node 833 (TableTree.node 829 (TableTree.node 827 (TableTree.leaf (42)) (TableTree.node 828 (TableTree.leaf (0)) (TableTree.leaf (0)))) (TableTree.node 831 (TableTree.node 830 (TableTree.leaf (42)) (TableTree.leaf (42))) (TableTree.node 832 (TableTree.leaf (0)) (TableTree.leaf (44))))) (TableTree.node 837 (TableTree.node 835 (TableTree.node 834 (TableTree.leaf (44)) (TableTree.leaf (44))) (TableTree.node 836 (TableTree.leaf (0)) (TableTree.leaf (0)))) (TableTree.node 839 (TableTree.node 838 (TableTree.leaf (44)) (TableTree.leaf (0))) (TableTree.node 840 (TableTree.leaf (0)) (TableTree.leaf (0))))))) (TableTree.node 855 (TableTree.node 848 (TableTree.node 844 (TableTree.node 842 (TableTree.leaf (0)) (TableTree.node 843 (TableTree.leaf (0)) (TableTree.leaf (0)))) (TableTree.node 846 (TableTree.node 845 (TableTree.leaf (0)) (TableTree.leaf (0))) (TableTree.node 847 (TableTree.leaf (0)) (TableTree.leaf (0))))) (TableTree.node 851 (TableTree.node 849 (TableTree.leaf (0)) (TableTree.node 850 (TableTree.leaf (44)) (TableTree.leaf (0)))) (TableTree.node 853 (TableTree.node 852 (TableTree.leaf (44)) (TableTree.leaf (0))) (TableTree.node 854 (TableTree.leaf (44)) (TableTree.leaf (44)))))) (TableTree.node 862 (TableTree.node 858 (TableTree.node 856 (TableTree.leaf (0)) (TableTree.node 857 (TableTree.leaf (0)) (TableTree.leaf (0)))) (TableTree.node 860 (TableTree.node 859 (TableTree.leaf (0)) (TableTree.leaf (0))) (TableTree.node 861 (TableTree.leaf (0)) (TableTree.leaf (42))))) (TableTree.node 866 (TableTree.node 864 (TableTree.node 863 (TableTree.leaf (0)) (TableTree.leaf (0))) (TableTree.node 865 (TableTree.leaf (0)) (TableTree.leaf (42)))) (TableTree.node 868 (TableTree.node 867 (TableTree.leaf (0)) (TableTree.leaf (42))) (TableTree.node 869 (TableTree.leaf (0)) (TableTree.leaf (0)))))))) (TableTree.node 899 (TableTree.node 884 (TableTree.node 877 (TableTree.node 873 (TableTree.node 871 (TableTree.leaf (44)) (TableTree.node 872 (TableTree.leaf (0)) (TableTree.leaf (44)))) (TableTree.node 875 (TableTree.node 874 (TableTree.leaf (0)) (TableTree.leaf (0))) (TableTree.node 876 (TableTree.leaf (42)) (TableTree.leaf (42))))) (TableTree.node 880 (TableTree.node 878 (TableTree.leaf (44)) (TableTree.node 879 (TableTree.leaf (42)) (TableTree.leaf (44)))) (TableTree.node 882 (TableTree.node 881 (TableTree.leaf (0)) (TableTree.leaf (0))) (TableTree.node 883 (TableTree.leaf (0)) (TableTree.leaf (0)))))) (TableTree.node 891 (TableTree.node 887 (TableTree.node 885 (TableTree.leaf (0)) (TableTree.node 886 (TableTree.leaf (42)) (TableTree.leaf (44)))) (TableTree.node 889 (TableTree.node 888 (TableTree.leaf (0)) (TableTree.leaf (44))) (TableTree.node 890 (TableTree.leaf (44)) (TableTree.leaf (0))))) (TableTree.node 895 (TableTree.node 893 (TableTree.node 892 (TableTree.leaf (0)) (TableTree.leaf (0))) (TableTree.node 894 (TableTree.leaf (0)) (TableTree.leaf (42)))) (TableTree.node 897 (TableTree.node 896 (TableTree.leaf (44)) (TableTree.leaf (0))) (TableTree.node 898 (TableTree.leaf (44)) (TableTree.leaf (44))))))) (TableTree.node 914 (TableTree.node 906 (TableTree.node 902 (TableTree.node 900 (TableTree.leaf (0)) (TableTree.node 901 (TableTree.leaf (0)) (TableTree.leaf (0)))) (TableTree.node 904 (TableTree.node 903 (TableTree.leaf (0)) (TableTree.leaf (42))) (TableTree.node 905 (TableTree.leaf (44)) (TableTree.leaf (0))))) (TableTree.node 910 (TableTree.node 908 (TableTree.node 907 (TableTree.leaf (44)) (TableTree.leaf (44))) (TableTree.node 909 (TableTree.leaf (0)) (TableTree.leaf (0)))) (TableTree.node 912 (TableTree.node 911 (TableTree.leaf (0)) (TableTree.leaf (0))) (TableTree.node 913 (TableTree.leaf (44)) (TableTree.leaf (44)))))) (TableTree.node 921 (TableTree.node 917 (TableTree.node 915 (TableTree.leaf (0)) (TableTree.node 916 (TableTree.leaf (44)) (TableTree.leaf (44)))) (TableTree.node 919 (TableTree.node 918 (TableTree.leaf (0)) (TableTree.leaf (0))) (TableTree.node 920 (TableTree.leaf (0)) (TableTree.leaf (0))))) (TableTree.node 925 (TableTree.node 923 (TableTree.node 922 (TableTree.leaf (42)) (TableTree.leaf (0))) (TableTree.node 924 (TableTree.leaf (42)) (TableTree.leaf (44)))) (TableTree.node 927 (TableTree.node 926 (TableTree.leaf (0)) (TableTree.leaf (0))) (TableTree.node 928 (TableTree.leaf (0)) (TableTree.leaf (0))))))))))))
private def finishAt (i : ℕ) : ℕ := if i < 929 then TableTree.lookup finishAtTree i else 0
private def jAtTree : TableTree (ℤ) := (TableTree.node 37 (TableTree.node 18 (TableTree.node 9 (TableTree.node 4 (TableTree.node 2 (TableTree.node 1 (TableTree.leaf (0)) (TableTree.leaf (96000))) (TableTree.node 3 (TableTree.leaf (-442203)) (TableTree.leaf (0)))) (TableTree.node 6 (TableTree.node 5 (TableTree.leaf (0)) (TableTree.leaf (-873000))) (TableTree.node 7 (TableTree.leaf (0)) (TableTree.node 8 (TableTree.leaf (0)) (TableTree.leaf (0)))))) (TableTree.node 13 (TableTree.node 11 (TableTree.node 10 (TableTree.leaf (0)) (TableTree.leaf (0))) (TableTree.node 12 (TableTree.leaf (0)) (TableTree.leaf (0)))) (TableTree.node 15 (TableTree.node 14 (TableTree.leaf (-984000)) (TableTree.leaf (0))) (TableTree.node 16 (TableTree.leaf (0)) (TableTree.node 17 (TableTree.leaf (0)) (TableTree.leaf (0))))))) (TableTree.node 27 (TableTree.node 22 (TableTree.node 20 (TableTree.node 19 (TableTree.leaf (0)) (TableTree.leaf (0))) (TableTree.node 21 (TableTree.leaf (-1095000)) (TableTree.leaf (0)))) (TableTree.node 24 (TableTree.node 23 (TableTree.leaf (0)) (TableTree.leaf (0))) (TableTree.node 25 (TableTree.leaf (0)) (TableTree.node 26 (TableTree.leaf (0)) (TableTree.leaf (0)))))) (TableTree.node 32 (TableTree.node 29 (TableTree.node 28 (TableTree.leaf (0)) (TableTree.leaf (0))) (TableTree.node 30 (TableTree.leaf (0)) (TableTree.node 31 (TableTree.leaf (0)) (TableTree.leaf (0))))) (TableTree.node 34 (TableTree.node 33 (TableTree.leaf (0)) (TableTree.leaf (0))) (TableTree.node 35 (TableTree.leaf (0)) (TableTree.node 36 (TableTree.leaf (0)) (TableTree.leaf (0)))))))) (TableTree.node 55 (TableTree.node 46 (TableTree.node 41 (TableTree.node 39 (TableTree.node 38 (TableTree.leaf (0)) (TableTree.leaf (0))) (TableTree.node 40 (TableTree.leaf (0)) (TableTree.leaf (0)))) (TableTree.node 43 (TableTree.node 42 (TableTree.leaf (0)) (TableTree.leaf (0))) (TableTree.node 44 (TableTree.leaf (0)) (TableTree.node 45 (TableTree.leaf (-1095000)) (TableTree.leaf (0)))))) (TableTree.node 50 (TableTree.node 48 (TableTree.node 47 (TableTree.leaf (0)) (TableTree.leaf (0))) (TableTree.node 49 (TableTree.leaf (0)) (TableTree.leaf (0)))) (TableTree.node 52 (TableTree.node 51 (TableTree.leaf (0)) (TableTree.leaf (0))) (TableTree.node 53 (TableTree.leaf (0)) (TableTree.node 54 (TableTree.leaf (0)) (TableTree.leaf (0))))))) (TableTree.node 64 (TableTree.node 59 (TableTree.node 57 (TableTree.node 56 (TableTree.leaf (0)) (TableTree.leaf (0))) (TableTree.node 58 (TableTree.leaf (0)) (TableTree.leaf (0)))) (TableTree.node 61 (TableTree.node 60 (TableTree.leaf (0)) (TableTree.leaf (0))) (TableTree.node 62 (TableTree.leaf (0)) (TableTree.node 63 (TableTree.leaf (0)) (TableTree.leaf (0)))))) (TableTree.node 69 (TableTree.node 66 (TableTree.node 65 (TableTree.leaf (0)) (TableTree.leaf (0))) (TableTree.node 67 (TableTree.leaf (0)) (TableTree.node 68 (TableTree.leaf (0)) (TableTree.leaf (0))))) (TableTree.node 71 (TableTree.node 70 (TableTree.leaf (0)) (TableTree.leaf (0))) (TableTree.node 72 (TableTree.leaf (0)) (TableTree.node 73 (TableTree.leaf (0)) (TableTree.leaf (0)))))))))
private def jAt (i : ℕ) : ℤ := if i < 74 then TableTree.lookup jAtTree i else 0
def digit (d : ℕ) : Fin 2 := if d=0 then 0 else 1
def nextList (s : Fin 74) (d : ℕ) : List (Fin 74) := (nextAt (s.val*2+(digit d).val)).map (Fin.ofNat 74)
def nextTable (s : Fin 74) (d : ℕ) : Finset (Fin 74) := (nextList s d).toFinset
def slot (s : Fin 74) (d : ℕ) (t : Fin 74) : ℕ := (nextList s d).idxOf t
def W (s : Fin 74) (d : ℕ) (t : Fin 74) : ℤ := (weightAt (s.val))[(digit d).val*3+slot s d t]?.getD 0
def source (p : Fin 929) : Fin 74 := Fin.ofNat 74 (sourceAt (p.val))
def carry (p : Fin 929) : ℕ := carryAt (p.val)
def endsList (p : Fin 929) : List (Fin 74) := (endAt (p.val)).map (Fin.ofNat 74)
def ends (p : Fin 929) : Finset (Fin 74) := (endsList p).toFinset
def eslot (p : Fin 929) (t : Fin 74) : ℕ := (endsList p).idxOf t
def H (p : Fin 929) (t : Fin 74) : ℤ := (hAt (p.val))[eslot p t]?.getD 0
def index (p : Fin 929) (d cp : ℕ) (sp : Fin 74) : ℕ := ((digit d).val*2+cp%2)*3+slot (source p) d sp
def target (p : Fin 929) (d cp : ℕ) (sp : Fin 74) : Fin 929 := Fin.ofNat 929 ((destAt (p.val))[index p d cp sp]?.getD 0)
def parent (p : Fin 929) (d cp : ℕ) (sp tp : Fin 74) : Fin 74 :=
  Fin.ofNat 74 ((parentAt (p.val))[(index p d cp sp)*3+eslot (target p d cp sp) tp]?.getD 0)
def finish (p : Fin 929) : Fin 74 := Fin.ofNat 74 (finishAt (p.val))
def J (s : Fin 74) : ℤ := jAt (s.val)
def F (s : Fin 74) : Prop := s.val ∉ [72]
instance (s : Fin 74) : Decidable (F s) := by unfold F; infer_instance
lemma next_nonempty : ∀ s (d : Fin 2), (nextTable s d.val).Nonempty := by decide +kernel

def D : Automaton (Fin 74) where
  start := 0
  next := nextTable
  nonempty s d := by
    by_cases hd : d=0
    · subst d; exact next_nonempty s 0
    · simpa only [nextTable,nextList,digit,if_neg hd] using next_nonempty s 1
  weight s d t := (W s d t:ℝ)/3000000

def R (s : Fin 74) (p : Fin 929) (c : ℕ) : Prop := s=source p ∧ c=carry p
instance (s : Fin 74) (p : Fin 929) (c : ℕ) : Decidable (R s p c) := by unfold R; infer_instance
lemma seed_relation_0 : R 0 0 0 := by decide +kernel
lemma seed_ends_0 : ∀ t ∈ ends 0, t=(0:Fin 74) := by decide +kernel
lemma seed_bound_0_0 : (0:ℤ) ≤ H 0 0 := by decide +kernel
lemma seed_run_0_0 : ∃ v,
    Run D D.start (Nat.digits 2 0).reverse 0 v ∧ v ≤ (H 0 0:ℝ)/3000000 := by
  refine ⟨((0:ℤ):ℝ)/3000000,?_,?_⟩
  · have he : (Nat.digits 2 0).reverse = [] := by decide +kernel
    rw [he]
    have hr := (Run.nil (D:=D) (0:Fin 74))
    convert hr using 1 <;> simp [D] <;> ring
  · have hh : ((0:ℤ):ℝ) ≤ H 0 0 := by exact_mod_cast seed_bound_0_0
    exact div_le_div_of_nonneg_right hh (by norm_num)
lemma seed_runs_0 : ∀ t ∈ ends 0, ∃ v,
    Run D D.start (Nat.digits 2 0).reverse t v ∧ v ≤ (H 0 t:ℝ)/3000000 := by
  intro t ht
  obtain rfl := seed_ends_0 t ht
  exact seed_run_0_0
lemma seed_relation_1 : R 0 1 1 := by decide +kernel
lemma seed_ends_1 : ∀ t ∈ ends 1, t=(1:Fin 74) := by decide +kernel
lemma seed_edge_1_0_0 : (1:Fin 74) ∈ D.next 0 1 := by decide +kernel
lemma seed_bound_1_0 : (W 0 1 1:ℤ) ≤ H 1 1 := by decide +kernel
lemma seed_run_1_0 : ∃ v,
    Run D D.start (Nat.digits 2 1).reverse 1 v ∧ v ≤ (H 1 1:ℝ)/3000000 := by
  refine ⟨((W 0 1 1:ℤ):ℝ)/3000000,?_,?_⟩
  · have he : (Nat.digits 2 1).reverse = [1] := by decide +kernel
    rw [he]
    have hr := (Run.cons seed_edge_1_0_0 (Run.nil (D:=D) (1:Fin 74)))
    convert hr using 1 <;> simp [D] <;> ring
  · have hh : ((W 0 1 1:ℤ):ℝ) ≤ H 1 1 := by exact_mod_cast seed_bound_1_0
    exact div_le_div_of_nonneg_right hh (by norm_num)
lemma seed_runs_1 : ∀ t ∈ ends 1, ∃ v,
    Run D D.start (Nat.digits 2 1).reverse t v ∧ v ≤ (H 1 t:ℝ)/3000000 := by
  intro t ht
  obtain rfl := seed_ends_1 t ht
  exact seed_run_1_0
lemma seed_relation_2 : R 0 2 2 := by decide +kernel
lemma seed_ends_2 : ∀ t ∈ ends 2, t=(2:Fin 74) := by decide +kernel
lemma seed_edge_2_0_0 : (1:Fin 74) ∈ D.next 0 1 := by decide +kernel
lemma seed_edge_2_0_1 : (2:Fin 74) ∈ D.next 1 0 := by decide +kernel
lemma seed_bound_2_0 : (W 0 1 1 + W 1 0 2:ℤ) ≤ H 2 2 := by decide +kernel
lemma seed_run_2_0 : ∃ v,
    Run D D.start (Nat.digits 2 2).reverse 2 v ∧ v ≤ (H 2 2:ℝ)/3000000 := by
  refine ⟨((W 0 1 1 + W 1 0 2:ℤ):ℝ)/3000000,?_,?_⟩
  · have he : (Nat.digits 2 2).reverse = [1,0] := by decide +kernel
    rw [he]
    have hr := (Run.cons seed_edge_2_0_0 (Run.cons seed_edge_2_0_1 (Run.nil (D:=D) (2:Fin 74))))
    convert hr using 1 <;> simp [D] <;> ring
  · have hh : ((W 0 1 1 + W 1 0 2:ℤ):ℝ) ≤ H 2 2 := by exact_mod_cast seed_bound_2_0
    exact div_le_div_of_nonneg_right hh (by norm_num)
lemma seed_runs_2 : ∀ t ∈ ends 2, ∃ v,
    Run D D.start (Nat.digits 2 2).reverse t v ∧ v ≤ (H 2 t:ℝ)/3000000 := by
  intro t ht
  obtain rfl := seed_ends_2 t ht
  exact seed_run_2_0
lemma seed_relation_3 : R 0 3 3 := by decide +kernel
lemma seed_ends_3 : ∀ t ∈ ends 3, t=(3:Fin 74) := by decide +kernel
lemma seed_edge_3_0_0 : (1:Fin 74) ∈ D.next 0 1 := by decide +kernel
lemma seed_edge_3_0_1 : (3:Fin 74) ∈ D.next 1 1 := by decide +kernel
lemma seed_bound_3_0 : (W 0 1 1 + W 1 1 3:ℤ) ≤ H 3 3 := by decide +kernel
lemma seed_run_3_0 : ∃ v,
    Run D D.start (Nat.digits 2 3).reverse 3 v ∧ v ≤ (H 3 3:ℝ)/3000000 := by
  refine ⟨((W 0 1 1 + W 1 1 3:ℤ):ℝ)/3000000,?_,?_⟩
  · have he : (Nat.digits 2 3).reverse = [1,1] := by decide +kernel
    rw [he]
    have hr := (Run.cons seed_edge_3_0_0 (Run.cons seed_edge_3_0_1 (Run.nil (D:=D) (3:Fin 74))))
    convert hr using 1 <;> simp [D] <;> ring
  · have hh : ((W 0 1 1 + W 1 1 3:ℤ):ℝ) ≤ H 3 3 := by exact_mod_cast seed_bound_3_0
    exact div_le_div_of_nonneg_right hh (by norm_num)
lemma seed_runs_3 : ∀ t ∈ ends 3, ∃ v,
    Run D D.start (Nat.digits 2 3).reverse t v ∧ v ≤ (H 3 t:ℝ)/3000000 := by
  intro t ht
  obtain rfl := seed_ends_3 t ht
  exact seed_run_3_0
lemma seed_relation_4 : R 0 4 4 := by decide +kernel
lemma seed_ends_4 : ∀ t ∈ ends 4, t=(5:Fin 74) := by decide +kernel
lemma seed_edge_4_0_0 : (1:Fin 74) ∈ D.next 0 1 := by decide +kernel
lemma seed_edge_4_0_1 : (2:Fin 74) ∈ D.next 1 0 := by decide +kernel
lemma seed_edge_4_0_2 : (5:Fin 74) ∈ D.next 2 0 := by decide +kernel
lemma seed_bound_4_0 : (W 0 1 1 + W 1 0 2 + W 2 0 5:ℤ) ≤ H 4 5 := by decide +kernel
lemma seed_run_4_0 : ∃ v,
    Run D D.start (Nat.digits 2 4).reverse 5 v ∧ v ≤ (H 4 5:ℝ)/3000000 := by
  refine ⟨((W 0 1 1 + W 1 0 2 + W 2 0 5:ℤ):ℝ)/3000000,?_,?_⟩
  · have he : (Nat.digits 2 4).reverse = [1,0,0] := by decide +kernel
    rw [he]
    have hr := (Run.cons seed_edge_4_0_0 (Run.cons seed_edge_4_0_1 (Run.cons seed_edge_4_0_2 (Run.nil (D:=D) (5:Fin 74)))))
    convert hr using 1 <;> simp [D] <;> ring
  · have hh : ((W 0 1 1 + W 1 0 2 + W 2 0 5:ℤ):ℝ) ≤ H 4 5 := by exact_mod_cast seed_bound_4_0
    exact div_le_div_of_nonneg_right hh (by norm_num)
lemma seed_runs_4 : ∀ t ∈ ends 4, ∃ v,
    Run D D.start (Nat.digits 2 4).reverse t v ∧ v ≤ (H 4 t:ℝ)/3000000 := by
  intro t ht
  obtain rfl := seed_ends_4 t ht
  exact seed_run_4_0
lemma seed_relation_5 : R 0 5 5 := by decide +kernel
lemma seed_ends_5 : ∀ t ∈ ends 5, t=(7:Fin 74) := by decide +kernel
lemma seed_edge_5_0_0 : (1:Fin 74) ∈ D.next 0 1 := by decide +kernel
lemma seed_edge_5_0_1 : (2:Fin 74) ∈ D.next 1 0 := by decide +kernel
lemma seed_edge_5_0_2 : (7:Fin 74) ∈ D.next 2 1 := by decide +kernel
lemma seed_bound_5_0 : (W 0 1 1 + W 1 0 2 + W 2 1 7:ℤ) ≤ H 5 7 := by decide +kernel
lemma seed_run_5_0 : ∃ v,
    Run D D.start (Nat.digits 2 5).reverse 7 v ∧ v ≤ (H 5 7:ℝ)/3000000 := by
  refine ⟨((W 0 1 1 + W 1 0 2 + W 2 1 7:ℤ):ℝ)/3000000,?_,?_⟩
  · have he : (Nat.digits 2 5).reverse = [1,0,1] := by decide +kernel
    rw [he]
    have hr := (Run.cons seed_edge_5_0_0 (Run.cons seed_edge_5_0_1 (Run.cons seed_edge_5_0_2 (Run.nil (D:=D) (7:Fin 74)))))
    convert hr using 1 <;> simp [D] <;> ring
  · have hh : ((W 0 1 1 + W 1 0 2 + W 2 1 7:ℤ):ℝ) ≤ H 5 7 := by exact_mod_cast seed_bound_5_0
    exact div_le_div_of_nonneg_right hh (by norm_num)
lemma seed_runs_5 : ∀ t ∈ ends 5, ∃ v,
    Run D D.start (Nat.digits 2 5).reverse t v ∧ v ≤ (H 5 t:ℝ)/3000000 := by
  intro t ht
  obtain rfl := seed_ends_5 t ht
  exact seed_run_5_0
lemma seed_relation_6 : R 0 6 6 := by decide +kernel
lemma seed_ends_6 : ∀ t ∈ ends 6, t=(8:Fin 74) := by decide +kernel
lemma seed_edge_6_0_0 : (1:Fin 74) ∈ D.next 0 1 := by decide +kernel
lemma seed_edge_6_0_1 : (3:Fin 74) ∈ D.next 1 1 := by decide +kernel
lemma seed_edge_6_0_2 : (8:Fin 74) ∈ D.next 3 0 := by decide +kernel
lemma seed_bound_6_0 : (W 0 1 1 + W 1 1 3 + W 3 0 8:ℤ) ≤ H 6 8 := by decide +kernel
lemma seed_run_6_0 : ∃ v,
    Run D D.start (Nat.digits 2 6).reverse 8 v ∧ v ≤ (H 6 8:ℝ)/3000000 := by
  refine ⟨((W 0 1 1 + W 1 1 3 + W 3 0 8:ℤ):ℝ)/3000000,?_,?_⟩
  · have he : (Nat.digits 2 6).reverse = [1,1,0] := by decide +kernel
    rw [he]
    have hr := (Run.cons seed_edge_6_0_0 (Run.cons seed_edge_6_0_1 (Run.cons seed_edge_6_0_2 (Run.nil (D:=D) (8:Fin 74)))))
    convert hr using 1 <;> simp [D] <;> ring
  · have hh : ((W 0 1 1 + W 1 1 3 + W 3 0 8:ℤ):ℝ) ≤ H 6 8 := by exact_mod_cast seed_bound_6_0
    exact div_le_div_of_nonneg_right hh (by norm_num)
lemma seed_runs_6 : ∀ t ∈ ends 6, ∃ v,
    Run D D.start (Nat.digits 2 6).reverse t v ∧ v ≤ (H 6 t:ℝ)/3000000 := by
  intro t ht
  obtain rfl := seed_ends_6 t ht
  exact seed_run_6_0
lemma seed_relation_7 : R 0 7 7 := by decide +kernel
lemma seed_ends_7 : ∀ t ∈ ends 7, t=(10:Fin 74) := by decide +kernel
lemma seed_edge_7_0_0 : (1:Fin 74) ∈ D.next 0 1 := by decide +kernel
lemma seed_edge_7_0_1 : (3:Fin 74) ∈ D.next 1 1 := by decide +kernel
lemma seed_edge_7_0_2 : (10:Fin 74) ∈ D.next 3 1 := by decide +kernel
lemma seed_bound_7_0 : (W 0 1 1 + W 1 1 3 + W 3 1 10:ℤ) ≤ H 7 10 := by decide +kernel
lemma seed_run_7_0 : ∃ v,
    Run D D.start (Nat.digits 2 7).reverse 10 v ∧ v ≤ (H 7 10:ℝ)/3000000 := by
  refine ⟨((W 0 1 1 + W 1 1 3 + W 3 1 10:ℤ):ℝ)/3000000,?_,?_⟩
  · have he : (Nat.digits 2 7).reverse = [1,1,1] := by decide +kernel
    rw [he]
    have hr := (Run.cons seed_edge_7_0_0 (Run.cons seed_edge_7_0_1 (Run.cons seed_edge_7_0_2 (Run.nil (D:=D) (10:Fin 74)))))
    convert hr using 1 <;> simp [D] <;> ring
  · have hh : ((W 0 1 1 + W 1 1 3 + W 3 1 10:ℤ):ℝ) ≤ H 7 10 := by exact_mod_cast seed_bound_7_0
    exact div_le_div_of_nonneg_right hh (by norm_num)
lemma seed_runs_7 : ∀ t ∈ ends 7, ∃ v,
    Run D D.start (Nat.digits 2 7).reverse t v ∧ v ≤ (H 7 t:ℝ)/3000000 := by
  intro t ht
  obtain rfl := seed_ends_7 t ht
  exact seed_run_7_0
lemma seed_relation_8 : R 0 8 8 := by decide +kernel
lemma seed_ends_8 : ∀ t ∈ ends 8, t=(13:Fin 74) := by decide +kernel
lemma seed_edge_8_0_0 : (1:Fin 74) ∈ D.next 0 1 := by decide +kernel
lemma seed_edge_8_0_1 : (2:Fin 74) ∈ D.next 1 0 := by decide +kernel
lemma seed_edge_8_0_2 : (5:Fin 74) ∈ D.next 2 0 := by decide +kernel
lemma seed_edge_8_0_3 : (13:Fin 74) ∈ D.next 5 0 := by decide +kernel
lemma seed_bound_8_0 : (W 0 1 1 + W 1 0 2 + W 2 0 5 + W 5 0 13:ℤ) ≤ H 8 13 := by decide +kernel
lemma seed_run_8_0 : ∃ v,
    Run D D.start (Nat.digits 2 8).reverse 13 v ∧ v ≤ (H 8 13:ℝ)/3000000 := by
  refine ⟨((W 0 1 1 + W 1 0 2 + W 2 0 5 + W 5 0 13:ℤ):ℝ)/3000000,?_,?_⟩
  · have he : (Nat.digits 2 8).reverse = [1,0,0,0] := by decide +kernel
    rw [he]
    have hr := (Run.cons seed_edge_8_0_0 (Run.cons seed_edge_8_0_1 (Run.cons seed_edge_8_0_2 (Run.cons seed_edge_8_0_3 (Run.nil (D:=D) (13:Fin 74))))))
    convert hr using 1 <;> simp [D] <;> ring
  · have hh : ((W 0 1 1 + W 1 0 2 + W 2 0 5 + W 5 0 13:ℤ):ℝ) ≤ H 8 13 := by exact_mod_cast seed_bound_8_0
    exact div_le_div_of_nonneg_right hh (by norm_num)
lemma seed_runs_8 : ∀ t ∈ ends 8, ∃ v,
    Run D D.start (Nat.digits 2 8).reverse t v ∧ v ≤ (H 8 t:ℝ)/3000000 := by
  intro t ht
  obtain rfl := seed_ends_8 t ht
  exact seed_run_8_0

def StepRow (p : Fin 929) : Prop := ∀ (d e : Fin 2) (cp : Fin 9),
    9*d.val+cp.val=2*carry p+e.val → ∀ sp ∈ D.next (source p) d.val,
    R sp (target p d.val cp.val sp) cp.val ∧
    ∀ tp ∈ ends (target p d.val cp.val sp),
      parent p d.val cp.val sp tp ∈ ends p ∧
      tp ∈ D.next (parent p d.val cp.val sp tp) e.val ∧
      H p (parent p d.val cp.val sp tp)+W (parent p d.val cp.val sp tp) e.val tp-
        W (source p) d.val sp ≤ H (target p d.val cp.val sp) tp

def stepCheck (p : Fin 929) : Bool :=
  ([0,1] : List ℕ).all fun d => ([0,1] : List ℕ).all fun e =>
    let cp := 2*carry p+e-9*d
    if 9*d ≤ 2*carry p+e ∧ cp < 9 then
      (nextList (source p) d).all fun sp =>
        decide (R sp (target p d cp sp) cp) &&
          (endsList (target p d cp sp)).all fun tp =>
            decide (parent p d cp sp tp ∈ ends p ∧
              tp ∈ D.next (parent p d cp sp tp) e ∧
              H p (parent p d cp sp tp)+W (parent p d cp sp tp) e tp-
                W (source p) d sp ≤ H (target p d cp sp) tp)
    else true

lemma step_check_chunk_0_small : ∀ p : Fin 4,
    stepCheck ⟨0+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_0 (p : Fin 929) (hl : 0 ≤ p.val) (hh : p.val < 4) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-0,by omega⟩
  have hp : (⟨0+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_0_small q

lemma step_check_chunk_1_small : ∀ p : Fin 4,
    stepCheck ⟨4+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_1 (p : Fin 929) (hl : 4 ≤ p.val) (hh : p.val < 8) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-4,by omega⟩
  have hp : (⟨4+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_1_small q

lemma step_check_chunk_2_small : ∀ p : Fin 4,
    stepCheck ⟨8+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_2 (p : Fin 929) (hl : 8 ≤ p.val) (hh : p.val < 12) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-8,by omega⟩
  have hp : (⟨8+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_2_small q

lemma step_check_chunk_3_small : ∀ p : Fin 4,
    stepCheck ⟨12+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_3 (p : Fin 929) (hl : 12 ≤ p.val) (hh : p.val < 16) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-12,by omega⟩
  have hp : (⟨12+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_3_small q

lemma step_check_chunk_4_small : ∀ p : Fin 4,
    stepCheck ⟨16+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_4 (p : Fin 929) (hl : 16 ≤ p.val) (hh : p.val < 20) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-16,by omega⟩
  have hp : (⟨16+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_4_small q

lemma step_check_chunk_5_small : ∀ p : Fin 4,
    stepCheck ⟨20+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_5 (p : Fin 929) (hl : 20 ≤ p.val) (hh : p.val < 24) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-20,by omega⟩
  have hp : (⟨20+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_5_small q

lemma step_check_chunk_6_small : ∀ p : Fin 4,
    stepCheck ⟨24+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_6 (p : Fin 929) (hl : 24 ≤ p.val) (hh : p.val < 28) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-24,by omega⟩
  have hp : (⟨24+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_6_small q

lemma step_check_chunk_7_small : ∀ p : Fin 4,
    stepCheck ⟨28+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_7 (p : Fin 929) (hl : 28 ≤ p.val) (hh : p.val < 32) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-28,by omega⟩
  have hp : (⟨28+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_7_small q

lemma step_check_chunk_8_small : ∀ p : Fin 4,
    stepCheck ⟨32+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_8 (p : Fin 929) (hl : 32 ≤ p.val) (hh : p.val < 36) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-32,by omega⟩
  have hp : (⟨32+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_8_small q

lemma step_check_chunk_9_small : ∀ p : Fin 4,
    stepCheck ⟨36+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_9 (p : Fin 929) (hl : 36 ≤ p.val) (hh : p.val < 40) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-36,by omega⟩
  have hp : (⟨36+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_9_small q

lemma step_check_chunk_10_small : ∀ p : Fin 4,
    stepCheck ⟨40+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_10 (p : Fin 929) (hl : 40 ≤ p.val) (hh : p.val < 44) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-40,by omega⟩
  have hp : (⟨40+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_10_small q

lemma step_check_chunk_11_small : ∀ p : Fin 4,
    stepCheck ⟨44+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_11 (p : Fin 929) (hl : 44 ≤ p.val) (hh : p.val < 48) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-44,by omega⟩
  have hp : (⟨44+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_11_small q

lemma step_check_chunk_12_small : ∀ p : Fin 4,
    stepCheck ⟨48+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_12 (p : Fin 929) (hl : 48 ≤ p.val) (hh : p.val < 52) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-48,by omega⟩
  have hp : (⟨48+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_12_small q

lemma step_check_chunk_13_small : ∀ p : Fin 4,
    stepCheck ⟨52+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_13 (p : Fin 929) (hl : 52 ≤ p.val) (hh : p.val < 56) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-52,by omega⟩
  have hp : (⟨52+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_13_small q

lemma step_check_chunk_14_small : ∀ p : Fin 4,
    stepCheck ⟨56+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_14 (p : Fin 929) (hl : 56 ≤ p.val) (hh : p.val < 60) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-56,by omega⟩
  have hp : (⟨56+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_14_small q

lemma step_check_chunk_15_small : ∀ p : Fin 4,
    stepCheck ⟨60+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_15 (p : Fin 929) (hl : 60 ≤ p.val) (hh : p.val < 64) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-60,by omega⟩
  have hp : (⟨60+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_15_small q

lemma step_check_chunk_16_small : ∀ p : Fin 4,
    stepCheck ⟨64+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_16 (p : Fin 929) (hl : 64 ≤ p.val) (hh : p.val < 68) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-64,by omega⟩
  have hp : (⟨64+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_16_small q

lemma step_check_chunk_17_small : ∀ p : Fin 4,
    stepCheck ⟨68+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_17 (p : Fin 929) (hl : 68 ≤ p.val) (hh : p.val < 72) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-68,by omega⟩
  have hp : (⟨68+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_17_small q

lemma step_check_chunk_18_small : ∀ p : Fin 4,
    stepCheck ⟨72+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_18 (p : Fin 929) (hl : 72 ≤ p.val) (hh : p.val < 76) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-72,by omega⟩
  have hp : (⟨72+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_18_small q

lemma step_check_chunk_19_small : ∀ p : Fin 4,
    stepCheck ⟨76+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_19 (p : Fin 929) (hl : 76 ≤ p.val) (hh : p.val < 80) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-76,by omega⟩
  have hp : (⟨76+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_19_small q

lemma step_check_chunk_20_small : ∀ p : Fin 4,
    stepCheck ⟨80+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_20 (p : Fin 929) (hl : 80 ≤ p.val) (hh : p.val < 84) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-80,by omega⟩
  have hp : (⟨80+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_20_small q

lemma step_check_chunk_21_small : ∀ p : Fin 4,
    stepCheck ⟨84+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_21 (p : Fin 929) (hl : 84 ≤ p.val) (hh : p.val < 88) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-84,by omega⟩
  have hp : (⟨84+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_21_small q

lemma step_check_chunk_22_small : ∀ p : Fin 4,
    stepCheck ⟨88+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_22 (p : Fin 929) (hl : 88 ≤ p.val) (hh : p.val < 92) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-88,by omega⟩
  have hp : (⟨88+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_22_small q

lemma step_check_chunk_23_small : ∀ p : Fin 4,
    stepCheck ⟨92+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_23 (p : Fin 929) (hl : 92 ≤ p.val) (hh : p.val < 96) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-92,by omega⟩
  have hp : (⟨92+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_23_small q

lemma step_check_chunk_24_small : ∀ p : Fin 4,
    stepCheck ⟨96+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_24 (p : Fin 929) (hl : 96 ≤ p.val) (hh : p.val < 100) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-96,by omega⟩
  have hp : (⟨96+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_24_small q

lemma step_check_chunk_25_small : ∀ p : Fin 4,
    stepCheck ⟨100+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_25 (p : Fin 929) (hl : 100 ≤ p.val) (hh : p.val < 104) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-100,by omega⟩
  have hp : (⟨100+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_25_small q

lemma step_check_chunk_26_small : ∀ p : Fin 4,
    stepCheck ⟨104+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_26 (p : Fin 929) (hl : 104 ≤ p.val) (hh : p.val < 108) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-104,by omega⟩
  have hp : (⟨104+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_26_small q

lemma step_check_chunk_27_small : ∀ p : Fin 4,
    stepCheck ⟨108+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_27 (p : Fin 929) (hl : 108 ≤ p.val) (hh : p.val < 112) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-108,by omega⟩
  have hp : (⟨108+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_27_small q

lemma step_check_chunk_28_small : ∀ p : Fin 4,
    stepCheck ⟨112+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_28 (p : Fin 929) (hl : 112 ≤ p.val) (hh : p.val < 116) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-112,by omega⟩
  have hp : (⟨112+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_28_small q

lemma step_check_chunk_29_small : ∀ p : Fin 4,
    stepCheck ⟨116+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_29 (p : Fin 929) (hl : 116 ≤ p.val) (hh : p.val < 120) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-116,by omega⟩
  have hp : (⟨116+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_29_small q

lemma step_check_chunk_30_small : ∀ p : Fin 4,
    stepCheck ⟨120+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_30 (p : Fin 929) (hl : 120 ≤ p.val) (hh : p.val < 124) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-120,by omega⟩
  have hp : (⟨120+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_30_small q

lemma step_check_chunk_31_small : ∀ p : Fin 4,
    stepCheck ⟨124+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_31 (p : Fin 929) (hl : 124 ≤ p.val) (hh : p.val < 128) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-124,by omega⟩
  have hp : (⟨124+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_31_small q

lemma step_check_chunk_32_small : ∀ p : Fin 4,
    stepCheck ⟨128+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_32 (p : Fin 929) (hl : 128 ≤ p.val) (hh : p.val < 132) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-128,by omega⟩
  have hp : (⟨128+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_32_small q

lemma step_check_chunk_33_small : ∀ p : Fin 4,
    stepCheck ⟨132+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_33 (p : Fin 929) (hl : 132 ≤ p.val) (hh : p.val < 136) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-132,by omega⟩
  have hp : (⟨132+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_33_small q

lemma step_check_chunk_34_small : ∀ p : Fin 4,
    stepCheck ⟨136+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_34 (p : Fin 929) (hl : 136 ≤ p.val) (hh : p.val < 140) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-136,by omega⟩
  have hp : (⟨136+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_34_small q

lemma step_check_chunk_35_small : ∀ p : Fin 4,
    stepCheck ⟨140+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_35 (p : Fin 929) (hl : 140 ≤ p.val) (hh : p.val < 144) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-140,by omega⟩
  have hp : (⟨140+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_35_small q

lemma step_check_chunk_36_small : ∀ p : Fin 4,
    stepCheck ⟨144+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_36 (p : Fin 929) (hl : 144 ≤ p.val) (hh : p.val < 148) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-144,by omega⟩
  have hp : (⟨144+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_36_small q

lemma step_check_chunk_37_small : ∀ p : Fin 4,
    stepCheck ⟨148+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_37 (p : Fin 929) (hl : 148 ≤ p.val) (hh : p.val < 152) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-148,by omega⟩
  have hp : (⟨148+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_37_small q

lemma step_check_chunk_38_small : ∀ p : Fin 4,
    stepCheck ⟨152+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_38 (p : Fin 929) (hl : 152 ≤ p.val) (hh : p.val < 156) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-152,by omega⟩
  have hp : (⟨152+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_38_small q

lemma step_check_chunk_39_small : ∀ p : Fin 4,
    stepCheck ⟨156+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_39 (p : Fin 929) (hl : 156 ≤ p.val) (hh : p.val < 160) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-156,by omega⟩
  have hp : (⟨156+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_39_small q

lemma step_check_chunk_40_small : ∀ p : Fin 4,
    stepCheck ⟨160+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_40 (p : Fin 929) (hl : 160 ≤ p.val) (hh : p.val < 164) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-160,by omega⟩
  have hp : (⟨160+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_40_small q

lemma step_check_chunk_41_small : ∀ p : Fin 4,
    stepCheck ⟨164+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_41 (p : Fin 929) (hl : 164 ≤ p.val) (hh : p.val < 168) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-164,by omega⟩
  have hp : (⟨164+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_41_small q

lemma step_check_chunk_42_small : ∀ p : Fin 4,
    stepCheck ⟨168+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_42 (p : Fin 929) (hl : 168 ≤ p.val) (hh : p.val < 172) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-168,by omega⟩
  have hp : (⟨168+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_42_small q

lemma step_check_chunk_43_small : ∀ p : Fin 4,
    stepCheck ⟨172+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_43 (p : Fin 929) (hl : 172 ≤ p.val) (hh : p.val < 176) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-172,by omega⟩
  have hp : (⟨172+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_43_small q

lemma step_check_chunk_44_small : ∀ p : Fin 4,
    stepCheck ⟨176+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_44 (p : Fin 929) (hl : 176 ≤ p.val) (hh : p.val < 180) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-176,by omega⟩
  have hp : (⟨176+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_44_small q

lemma step_check_chunk_45_small : ∀ p : Fin 4,
    stepCheck ⟨180+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_45 (p : Fin 929) (hl : 180 ≤ p.val) (hh : p.val < 184) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-180,by omega⟩
  have hp : (⟨180+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_45_small q

lemma step_check_chunk_46_small : ∀ p : Fin 4,
    stepCheck ⟨184+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_46 (p : Fin 929) (hl : 184 ≤ p.val) (hh : p.val < 188) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-184,by omega⟩
  have hp : (⟨184+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_46_small q

lemma step_check_chunk_47_small : ∀ p : Fin 4,
    stepCheck ⟨188+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_47 (p : Fin 929) (hl : 188 ≤ p.val) (hh : p.val < 192) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-188,by omega⟩
  have hp : (⟨188+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_47_small q

lemma step_check_chunk_48_small : ∀ p : Fin 4,
    stepCheck ⟨192+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_48 (p : Fin 929) (hl : 192 ≤ p.val) (hh : p.val < 196) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-192,by omega⟩
  have hp : (⟨192+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_48_small q

lemma step_check_chunk_49_small : ∀ p : Fin 4,
    stepCheck ⟨196+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_49 (p : Fin 929) (hl : 196 ≤ p.val) (hh : p.val < 200) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-196,by omega⟩
  have hp : (⟨196+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_49_small q

lemma step_check_chunk_50_small : ∀ p : Fin 4,
    stepCheck ⟨200+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_50 (p : Fin 929) (hl : 200 ≤ p.val) (hh : p.val < 204) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-200,by omega⟩
  have hp : (⟨200+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_50_small q

lemma step_check_chunk_51_small : ∀ p : Fin 4,
    stepCheck ⟨204+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_51 (p : Fin 929) (hl : 204 ≤ p.val) (hh : p.val < 208) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-204,by omega⟩
  have hp : (⟨204+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_51_small q

lemma step_check_chunk_52_small : ∀ p : Fin 4,
    stepCheck ⟨208+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_52 (p : Fin 929) (hl : 208 ≤ p.val) (hh : p.val < 212) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-208,by omega⟩
  have hp : (⟨208+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_52_small q

lemma step_check_chunk_53_small : ∀ p : Fin 4,
    stepCheck ⟨212+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_53 (p : Fin 929) (hl : 212 ≤ p.val) (hh : p.val < 216) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-212,by omega⟩
  have hp : (⟨212+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_53_small q

lemma step_check_chunk_54_small : ∀ p : Fin 4,
    stepCheck ⟨216+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_54 (p : Fin 929) (hl : 216 ≤ p.val) (hh : p.val < 220) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-216,by omega⟩
  have hp : (⟨216+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_54_small q

lemma step_check_chunk_55_small : ∀ p : Fin 4,
    stepCheck ⟨220+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_55 (p : Fin 929) (hl : 220 ≤ p.val) (hh : p.val < 224) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-220,by omega⟩
  have hp : (⟨220+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_55_small q

lemma step_check_chunk_56_small : ∀ p : Fin 4,
    stepCheck ⟨224+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_56 (p : Fin 929) (hl : 224 ≤ p.val) (hh : p.val < 228) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-224,by omega⟩
  have hp : (⟨224+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_56_small q

lemma step_check_chunk_57_small : ∀ p : Fin 4,
    stepCheck ⟨228+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_57 (p : Fin 929) (hl : 228 ≤ p.val) (hh : p.val < 232) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-228,by omega⟩
  have hp : (⟨228+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_57_small q

lemma step_check_chunk_58_small : ∀ p : Fin 4,
    stepCheck ⟨232+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_58 (p : Fin 929) (hl : 232 ≤ p.val) (hh : p.val < 236) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-232,by omega⟩
  have hp : (⟨232+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_58_small q

lemma step_check_chunk_59_small : ∀ p : Fin 4,
    stepCheck ⟨236+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_59 (p : Fin 929) (hl : 236 ≤ p.val) (hh : p.val < 240) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-236,by omega⟩
  have hp : (⟨236+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_59_small q

lemma step_check_chunk_60_small : ∀ p : Fin 4,
    stepCheck ⟨240+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_60 (p : Fin 929) (hl : 240 ≤ p.val) (hh : p.val < 244) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-240,by omega⟩
  have hp : (⟨240+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_60_small q

lemma step_check_chunk_61_small : ∀ p : Fin 4,
    stepCheck ⟨244+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_61 (p : Fin 929) (hl : 244 ≤ p.val) (hh : p.val < 248) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-244,by omega⟩
  have hp : (⟨244+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_61_small q

lemma step_check_chunk_62_small : ∀ p : Fin 4,
    stepCheck ⟨248+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_62 (p : Fin 929) (hl : 248 ≤ p.val) (hh : p.val < 252) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-248,by omega⟩
  have hp : (⟨248+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_62_small q

lemma step_check_chunk_63_small : ∀ p : Fin 4,
    stepCheck ⟨252+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_63 (p : Fin 929) (hl : 252 ≤ p.val) (hh : p.val < 256) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-252,by omega⟩
  have hp : (⟨252+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_63_small q

lemma step_check_chunk_64_small : ∀ p : Fin 4,
    stepCheck ⟨256+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_64 (p : Fin 929) (hl : 256 ≤ p.val) (hh : p.val < 260) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-256,by omega⟩
  have hp : (⟨256+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_64_small q

lemma step_check_chunk_65_small : ∀ p : Fin 4,
    stepCheck ⟨260+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_65 (p : Fin 929) (hl : 260 ≤ p.val) (hh : p.val < 264) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-260,by omega⟩
  have hp : (⟨260+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_65_small q

lemma step_check_chunk_66_small : ∀ p : Fin 4,
    stepCheck ⟨264+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_66 (p : Fin 929) (hl : 264 ≤ p.val) (hh : p.val < 268) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-264,by omega⟩
  have hp : (⟨264+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_66_small q

lemma step_check_chunk_67_small : ∀ p : Fin 4,
    stepCheck ⟨268+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_67 (p : Fin 929) (hl : 268 ≤ p.val) (hh : p.val < 272) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-268,by omega⟩
  have hp : (⟨268+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_67_small q

lemma step_check_chunk_68_small : ∀ p : Fin 4,
    stepCheck ⟨272+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_68 (p : Fin 929) (hl : 272 ≤ p.val) (hh : p.val < 276) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-272,by omega⟩
  have hp : (⟨272+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_68_small q

lemma step_check_chunk_69_small : ∀ p : Fin 4,
    stepCheck ⟨276+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_69 (p : Fin 929) (hl : 276 ≤ p.val) (hh : p.val < 280) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-276,by omega⟩
  have hp : (⟨276+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_69_small q

lemma step_check_chunk_70_small : ∀ p : Fin 4,
    stepCheck ⟨280+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_70 (p : Fin 929) (hl : 280 ≤ p.val) (hh : p.val < 284) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-280,by omega⟩
  have hp : (⟨280+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_70_small q

lemma step_check_chunk_71_small : ∀ p : Fin 4,
    stepCheck ⟨284+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_71 (p : Fin 929) (hl : 284 ≤ p.val) (hh : p.val < 288) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-284,by omega⟩
  have hp : (⟨284+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_71_small q

lemma step_check_chunk_72_small : ∀ p : Fin 4,
    stepCheck ⟨288+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_72 (p : Fin 929) (hl : 288 ≤ p.val) (hh : p.val < 292) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-288,by omega⟩
  have hp : (⟨288+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_72_small q

lemma step_check_chunk_73_small : ∀ p : Fin 4,
    stepCheck ⟨292+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_73 (p : Fin 929) (hl : 292 ≤ p.val) (hh : p.val < 296) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-292,by omega⟩
  have hp : (⟨292+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_73_small q

lemma step_check_chunk_74_small : ∀ p : Fin 4,
    stepCheck ⟨296+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_74 (p : Fin 929) (hl : 296 ≤ p.val) (hh : p.val < 300) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-296,by omega⟩
  have hp : (⟨296+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_74_small q

lemma step_check_chunk_75_small : ∀ p : Fin 4,
    stepCheck ⟨300+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_75 (p : Fin 929) (hl : 300 ≤ p.val) (hh : p.val < 304) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-300,by omega⟩
  have hp : (⟨300+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_75_small q

lemma step_check_chunk_76_small : ∀ p : Fin 4,
    stepCheck ⟨304+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_76 (p : Fin 929) (hl : 304 ≤ p.val) (hh : p.val < 308) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-304,by omega⟩
  have hp : (⟨304+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_76_small q

lemma step_check_chunk_77_small : ∀ p : Fin 4,
    stepCheck ⟨308+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_77 (p : Fin 929) (hl : 308 ≤ p.val) (hh : p.val < 312) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-308,by omega⟩
  have hp : (⟨308+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_77_small q

lemma step_check_chunk_78_small : ∀ p : Fin 4,
    stepCheck ⟨312+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_78 (p : Fin 929) (hl : 312 ≤ p.val) (hh : p.val < 316) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-312,by omega⟩
  have hp : (⟨312+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_78_small q

lemma step_check_chunk_79_small : ∀ p : Fin 4,
    stepCheck ⟨316+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_79 (p : Fin 929) (hl : 316 ≤ p.val) (hh : p.val < 320) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-316,by omega⟩
  have hp : (⟨316+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_79_small q

lemma step_check_chunk_80_small : ∀ p : Fin 4,
    stepCheck ⟨320+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_80 (p : Fin 929) (hl : 320 ≤ p.val) (hh : p.val < 324) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-320,by omega⟩
  have hp : (⟨320+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_80_small q

lemma step_check_chunk_81_small : ∀ p : Fin 4,
    stepCheck ⟨324+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_81 (p : Fin 929) (hl : 324 ≤ p.val) (hh : p.val < 328) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-324,by omega⟩
  have hp : (⟨324+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_81_small q

lemma step_check_chunk_82_small : ∀ p : Fin 4,
    stepCheck ⟨328+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_82 (p : Fin 929) (hl : 328 ≤ p.val) (hh : p.val < 332) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-328,by omega⟩
  have hp : (⟨328+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_82_small q

lemma step_check_chunk_83_small : ∀ p : Fin 4,
    stepCheck ⟨332+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_83 (p : Fin 929) (hl : 332 ≤ p.val) (hh : p.val < 336) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-332,by omega⟩
  have hp : (⟨332+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_83_small q

lemma step_check_chunk_84_small : ∀ p : Fin 4,
    stepCheck ⟨336+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_84 (p : Fin 929) (hl : 336 ≤ p.val) (hh : p.val < 340) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-336,by omega⟩
  have hp : (⟨336+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_84_small q

lemma step_check_chunk_85_small : ∀ p : Fin 4,
    stepCheck ⟨340+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_85 (p : Fin 929) (hl : 340 ≤ p.val) (hh : p.val < 344) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-340,by omega⟩
  have hp : (⟨340+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_85_small q

lemma step_check_chunk_86_small : ∀ p : Fin 4,
    stepCheck ⟨344+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_86 (p : Fin 929) (hl : 344 ≤ p.val) (hh : p.val < 348) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-344,by omega⟩
  have hp : (⟨344+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_86_small q

lemma step_check_chunk_87_small : ∀ p : Fin 4,
    stepCheck ⟨348+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_87 (p : Fin 929) (hl : 348 ≤ p.val) (hh : p.val < 352) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-348,by omega⟩
  have hp : (⟨348+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_87_small q

lemma step_check_chunk_88_small : ∀ p : Fin 4,
    stepCheck ⟨352+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_88 (p : Fin 929) (hl : 352 ≤ p.val) (hh : p.val < 356) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-352,by omega⟩
  have hp : (⟨352+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_88_small q

lemma step_check_chunk_89_small : ∀ p : Fin 4,
    stepCheck ⟨356+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_89 (p : Fin 929) (hl : 356 ≤ p.val) (hh : p.val < 360) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-356,by omega⟩
  have hp : (⟨356+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_89_small q

lemma step_check_chunk_90_small : ∀ p : Fin 4,
    stepCheck ⟨360+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_90 (p : Fin 929) (hl : 360 ≤ p.val) (hh : p.val < 364) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-360,by omega⟩
  have hp : (⟨360+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_90_small q

lemma step_check_chunk_91_small : ∀ p : Fin 4,
    stepCheck ⟨364+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_91 (p : Fin 929) (hl : 364 ≤ p.val) (hh : p.val < 368) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-364,by omega⟩
  have hp : (⟨364+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_91_small q

lemma step_check_chunk_92_small : ∀ p : Fin 4,
    stepCheck ⟨368+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_92 (p : Fin 929) (hl : 368 ≤ p.val) (hh : p.val < 372) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-368,by omega⟩
  have hp : (⟨368+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_92_small q

lemma step_check_chunk_93_small : ∀ p : Fin 4,
    stepCheck ⟨372+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_93 (p : Fin 929) (hl : 372 ≤ p.val) (hh : p.val < 376) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-372,by omega⟩
  have hp : (⟨372+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_93_small q

lemma step_check_chunk_94_small : ∀ p : Fin 4,
    stepCheck ⟨376+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_94 (p : Fin 929) (hl : 376 ≤ p.val) (hh : p.val < 380) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-376,by omega⟩
  have hp : (⟨376+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_94_small q

lemma step_check_chunk_95_small : ∀ p : Fin 4,
    stepCheck ⟨380+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_95 (p : Fin 929) (hl : 380 ≤ p.val) (hh : p.val < 384) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-380,by omega⟩
  have hp : (⟨380+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_95_small q

lemma step_check_chunk_96_small : ∀ p : Fin 4,
    stepCheck ⟨384+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_96 (p : Fin 929) (hl : 384 ≤ p.val) (hh : p.val < 388) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-384,by omega⟩
  have hp : (⟨384+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_96_small q

lemma step_check_chunk_97_small : ∀ p : Fin 4,
    stepCheck ⟨388+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_97 (p : Fin 929) (hl : 388 ≤ p.val) (hh : p.val < 392) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-388,by omega⟩
  have hp : (⟨388+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_97_small q

lemma step_check_chunk_98_small : ∀ p : Fin 4,
    stepCheck ⟨392+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_98 (p : Fin 929) (hl : 392 ≤ p.val) (hh : p.val < 396) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-392,by omega⟩
  have hp : (⟨392+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_98_small q

lemma step_check_chunk_99_small : ∀ p : Fin 4,
    stepCheck ⟨396+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_99 (p : Fin 929) (hl : 396 ≤ p.val) (hh : p.val < 400) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-396,by omega⟩
  have hp : (⟨396+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_99_small q

lemma step_check_chunk_100_small : ∀ p : Fin 4,
    stepCheck ⟨400+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_100 (p : Fin 929) (hl : 400 ≤ p.val) (hh : p.val < 404) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-400,by omega⟩
  have hp : (⟨400+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_100_small q

lemma step_check_chunk_101_small : ∀ p : Fin 4,
    stepCheck ⟨404+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_101 (p : Fin 929) (hl : 404 ≤ p.val) (hh : p.val < 408) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-404,by omega⟩
  have hp : (⟨404+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_101_small q

lemma step_check_chunk_102_small : ∀ p : Fin 4,
    stepCheck ⟨408+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_102 (p : Fin 929) (hl : 408 ≤ p.val) (hh : p.val < 412) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-408,by omega⟩
  have hp : (⟨408+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_102_small q

lemma step_check_chunk_103_small : ∀ p : Fin 4,
    stepCheck ⟨412+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_103 (p : Fin 929) (hl : 412 ≤ p.val) (hh : p.val < 416) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-412,by omega⟩
  have hp : (⟨412+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_103_small q

lemma step_check_chunk_104_small : ∀ p : Fin 4,
    stepCheck ⟨416+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_104 (p : Fin 929) (hl : 416 ≤ p.val) (hh : p.val < 420) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-416,by omega⟩
  have hp : (⟨416+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_104_small q

lemma step_check_chunk_105_small : ∀ p : Fin 4,
    stepCheck ⟨420+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_105 (p : Fin 929) (hl : 420 ≤ p.val) (hh : p.val < 424) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-420,by omega⟩
  have hp : (⟨420+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_105_small q

lemma step_check_chunk_106_small : ∀ p : Fin 4,
    stepCheck ⟨424+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_106 (p : Fin 929) (hl : 424 ≤ p.val) (hh : p.val < 428) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-424,by omega⟩
  have hp : (⟨424+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_106_small q

lemma step_check_chunk_107_small : ∀ p : Fin 4,
    stepCheck ⟨428+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_107 (p : Fin 929) (hl : 428 ≤ p.val) (hh : p.val < 432) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-428,by omega⟩
  have hp : (⟨428+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_107_small q

lemma step_check_chunk_108_small : ∀ p : Fin 4,
    stepCheck ⟨432+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_108 (p : Fin 929) (hl : 432 ≤ p.val) (hh : p.val < 436) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-432,by omega⟩
  have hp : (⟨432+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_108_small q

lemma step_check_chunk_109_small : ∀ p : Fin 4,
    stepCheck ⟨436+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_109 (p : Fin 929) (hl : 436 ≤ p.val) (hh : p.val < 440) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-436,by omega⟩
  have hp : (⟨436+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_109_small q

lemma step_check_chunk_110_small : ∀ p : Fin 4,
    stepCheck ⟨440+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_110 (p : Fin 929) (hl : 440 ≤ p.val) (hh : p.val < 444) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-440,by omega⟩
  have hp : (⟨440+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_110_small q

lemma step_check_chunk_111_small : ∀ p : Fin 4,
    stepCheck ⟨444+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_111 (p : Fin 929) (hl : 444 ≤ p.val) (hh : p.val < 448) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-444,by omega⟩
  have hp : (⟨444+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_111_small q

lemma step_check_chunk_112_small : ∀ p : Fin 4,
    stepCheck ⟨448+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_112 (p : Fin 929) (hl : 448 ≤ p.val) (hh : p.val < 452) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-448,by omega⟩
  have hp : (⟨448+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_112_small q

lemma step_check_chunk_113_small : ∀ p : Fin 4,
    stepCheck ⟨452+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_113 (p : Fin 929) (hl : 452 ≤ p.val) (hh : p.val < 456) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-452,by omega⟩
  have hp : (⟨452+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_113_small q

lemma step_check_chunk_114_small : ∀ p : Fin 4,
    stepCheck ⟨456+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_114 (p : Fin 929) (hl : 456 ≤ p.val) (hh : p.val < 460) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-456,by omega⟩
  have hp : (⟨456+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_114_small q

lemma step_check_chunk_115_small : ∀ p : Fin 4,
    stepCheck ⟨460+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_115 (p : Fin 929) (hl : 460 ≤ p.val) (hh : p.val < 464) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-460,by omega⟩
  have hp : (⟨460+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_115_small q

lemma step_check_chunk_116_small : ∀ p : Fin 4,
    stepCheck ⟨464+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_116 (p : Fin 929) (hl : 464 ≤ p.val) (hh : p.val < 468) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-464,by omega⟩
  have hp : (⟨464+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_116_small q

lemma step_check_chunk_117_small : ∀ p : Fin 4,
    stepCheck ⟨468+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_117 (p : Fin 929) (hl : 468 ≤ p.val) (hh : p.val < 472) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-468,by omega⟩
  have hp : (⟨468+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_117_small q

lemma step_check_chunk_118_small : ∀ p : Fin 4,
    stepCheck ⟨472+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_118 (p : Fin 929) (hl : 472 ≤ p.val) (hh : p.val < 476) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-472,by omega⟩
  have hp : (⟨472+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_118_small q

lemma step_check_chunk_119_small : ∀ p : Fin 4,
    stepCheck ⟨476+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_119 (p : Fin 929) (hl : 476 ≤ p.val) (hh : p.val < 480) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-476,by omega⟩
  have hp : (⟨476+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_119_small q

lemma step_check_chunk_120_small : ∀ p : Fin 4,
    stepCheck ⟨480+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_120 (p : Fin 929) (hl : 480 ≤ p.val) (hh : p.val < 484) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-480,by omega⟩
  have hp : (⟨480+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_120_small q

lemma step_check_chunk_121_small : ∀ p : Fin 4,
    stepCheck ⟨484+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_121 (p : Fin 929) (hl : 484 ≤ p.val) (hh : p.val < 488) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-484,by omega⟩
  have hp : (⟨484+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_121_small q

lemma step_check_chunk_122_small : ∀ p : Fin 4,
    stepCheck ⟨488+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_122 (p : Fin 929) (hl : 488 ≤ p.val) (hh : p.val < 492) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-488,by omega⟩
  have hp : (⟨488+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_122_small q

lemma step_check_chunk_123_small : ∀ p : Fin 4,
    stepCheck ⟨492+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_123 (p : Fin 929) (hl : 492 ≤ p.val) (hh : p.val < 496) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-492,by omega⟩
  have hp : (⟨492+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_123_small q

lemma step_check_chunk_124_small : ∀ p : Fin 4,
    stepCheck ⟨496+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_124 (p : Fin 929) (hl : 496 ≤ p.val) (hh : p.val < 500) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-496,by omega⟩
  have hp : (⟨496+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_124_small q

lemma step_check_chunk_125_small : ∀ p : Fin 4,
    stepCheck ⟨500+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_125 (p : Fin 929) (hl : 500 ≤ p.val) (hh : p.val < 504) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-500,by omega⟩
  have hp : (⟨500+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_125_small q

lemma step_check_chunk_126_small : ∀ p : Fin 4,
    stepCheck ⟨504+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_126 (p : Fin 929) (hl : 504 ≤ p.val) (hh : p.val < 508) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-504,by omega⟩
  have hp : (⟨504+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_126_small q

lemma step_check_chunk_127_small : ∀ p : Fin 4,
    stepCheck ⟨508+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_127 (p : Fin 929) (hl : 508 ≤ p.val) (hh : p.val < 512) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-508,by omega⟩
  have hp : (⟨508+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_127_small q

lemma step_check_chunk_128_small : ∀ p : Fin 4,
    stepCheck ⟨512+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_128 (p : Fin 929) (hl : 512 ≤ p.val) (hh : p.val < 516) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-512,by omega⟩
  have hp : (⟨512+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_128_small q

lemma step_check_chunk_129_small : ∀ p : Fin 4,
    stepCheck ⟨516+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_129 (p : Fin 929) (hl : 516 ≤ p.val) (hh : p.val < 520) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-516,by omega⟩
  have hp : (⟨516+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_129_small q

lemma step_check_chunk_130_small : ∀ p : Fin 4,
    stepCheck ⟨520+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_130 (p : Fin 929) (hl : 520 ≤ p.val) (hh : p.val < 524) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-520,by omega⟩
  have hp : (⟨520+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_130_small q

lemma step_check_chunk_131_small : ∀ p : Fin 4,
    stepCheck ⟨524+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_131 (p : Fin 929) (hl : 524 ≤ p.val) (hh : p.val < 528) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-524,by omega⟩
  have hp : (⟨524+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_131_small q

lemma step_check_chunk_132_small : ∀ p : Fin 4,
    stepCheck ⟨528+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_132 (p : Fin 929) (hl : 528 ≤ p.val) (hh : p.val < 532) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-528,by omega⟩
  have hp : (⟨528+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_132_small q

lemma step_check_chunk_133_small : ∀ p : Fin 4,
    stepCheck ⟨532+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_133 (p : Fin 929) (hl : 532 ≤ p.val) (hh : p.val < 536) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-532,by omega⟩
  have hp : (⟨532+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_133_small q

lemma step_check_chunk_134_small : ∀ p : Fin 4,
    stepCheck ⟨536+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_134 (p : Fin 929) (hl : 536 ≤ p.val) (hh : p.val < 540) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-536,by omega⟩
  have hp : (⟨536+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_134_small q

lemma step_check_chunk_135_small : ∀ p : Fin 4,
    stepCheck ⟨540+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_135 (p : Fin 929) (hl : 540 ≤ p.val) (hh : p.val < 544) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-540,by omega⟩
  have hp : (⟨540+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_135_small q

lemma step_check_chunk_136_small : ∀ p : Fin 4,
    stepCheck ⟨544+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_136 (p : Fin 929) (hl : 544 ≤ p.val) (hh : p.val < 548) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-544,by omega⟩
  have hp : (⟨544+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_136_small q

lemma step_check_chunk_137_small : ∀ p : Fin 4,
    stepCheck ⟨548+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_137 (p : Fin 929) (hl : 548 ≤ p.val) (hh : p.val < 552) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-548,by omega⟩
  have hp : (⟨548+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_137_small q

lemma step_check_chunk_138_small : ∀ p : Fin 4,
    stepCheck ⟨552+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_138 (p : Fin 929) (hl : 552 ≤ p.val) (hh : p.val < 556) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-552,by omega⟩
  have hp : (⟨552+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_138_small q

lemma step_check_chunk_139_small : ∀ p : Fin 4,
    stepCheck ⟨556+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_139 (p : Fin 929) (hl : 556 ≤ p.val) (hh : p.val < 560) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-556,by omega⟩
  have hp : (⟨556+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_139_small q

lemma step_check_chunk_140_small : ∀ p : Fin 4,
    stepCheck ⟨560+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_140 (p : Fin 929) (hl : 560 ≤ p.val) (hh : p.val < 564) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-560,by omega⟩
  have hp : (⟨560+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_140_small q

lemma step_check_chunk_141_small : ∀ p : Fin 4,
    stepCheck ⟨564+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_141 (p : Fin 929) (hl : 564 ≤ p.val) (hh : p.val < 568) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-564,by omega⟩
  have hp : (⟨564+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_141_small q

lemma step_check_chunk_142_small : ∀ p : Fin 4,
    stepCheck ⟨568+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_142 (p : Fin 929) (hl : 568 ≤ p.val) (hh : p.val < 572) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-568,by omega⟩
  have hp : (⟨568+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_142_small q

lemma step_check_chunk_143_small : ∀ p : Fin 4,
    stepCheck ⟨572+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_143 (p : Fin 929) (hl : 572 ≤ p.val) (hh : p.val < 576) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-572,by omega⟩
  have hp : (⟨572+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_143_small q

lemma step_check_chunk_144_small : ∀ p : Fin 4,
    stepCheck ⟨576+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_144 (p : Fin 929) (hl : 576 ≤ p.val) (hh : p.val < 580) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-576,by omega⟩
  have hp : (⟨576+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_144_small q

lemma step_check_chunk_145_small : ∀ p : Fin 4,
    stepCheck ⟨580+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_145 (p : Fin 929) (hl : 580 ≤ p.val) (hh : p.val < 584) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-580,by omega⟩
  have hp : (⟨580+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_145_small q

lemma step_check_chunk_146_small : ∀ p : Fin 4,
    stepCheck ⟨584+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_146 (p : Fin 929) (hl : 584 ≤ p.val) (hh : p.val < 588) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-584,by omega⟩
  have hp : (⟨584+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_146_small q

lemma step_check_chunk_147_small : ∀ p : Fin 4,
    stepCheck ⟨588+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_147 (p : Fin 929) (hl : 588 ≤ p.val) (hh : p.val < 592) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-588,by omega⟩
  have hp : (⟨588+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_147_small q

lemma step_check_chunk_148_small : ∀ p : Fin 4,
    stepCheck ⟨592+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_148 (p : Fin 929) (hl : 592 ≤ p.val) (hh : p.val < 596) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-592,by omega⟩
  have hp : (⟨592+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_148_small q

lemma step_check_chunk_149_small : ∀ p : Fin 4,
    stepCheck ⟨596+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_149 (p : Fin 929) (hl : 596 ≤ p.val) (hh : p.val < 600) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-596,by omega⟩
  have hp : (⟨596+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_149_small q

lemma step_check_chunk_150_small : ∀ p : Fin 4,
    stepCheck ⟨600+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_150 (p : Fin 929) (hl : 600 ≤ p.val) (hh : p.val < 604) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-600,by omega⟩
  have hp : (⟨600+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_150_small q

lemma step_check_chunk_151_small : ∀ p : Fin 4,
    stepCheck ⟨604+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_151 (p : Fin 929) (hl : 604 ≤ p.val) (hh : p.val < 608) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-604,by omega⟩
  have hp : (⟨604+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_151_small q

lemma step_check_chunk_152_small : ∀ p : Fin 4,
    stepCheck ⟨608+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_152 (p : Fin 929) (hl : 608 ≤ p.val) (hh : p.val < 612) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-608,by omega⟩
  have hp : (⟨608+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_152_small q

lemma step_check_chunk_153_small : ∀ p : Fin 4,
    stepCheck ⟨612+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_153 (p : Fin 929) (hl : 612 ≤ p.val) (hh : p.val < 616) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-612,by omega⟩
  have hp : (⟨612+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_153_small q

lemma step_check_chunk_154_small : ∀ p : Fin 4,
    stepCheck ⟨616+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_154 (p : Fin 929) (hl : 616 ≤ p.val) (hh : p.val < 620) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-616,by omega⟩
  have hp : (⟨616+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_154_small q

lemma step_check_chunk_155_small : ∀ p : Fin 4,
    stepCheck ⟨620+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_155 (p : Fin 929) (hl : 620 ≤ p.val) (hh : p.val < 624) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-620,by omega⟩
  have hp : (⟨620+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_155_small q

lemma step_check_chunk_156_small : ∀ p : Fin 4,
    stepCheck ⟨624+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_156 (p : Fin 929) (hl : 624 ≤ p.val) (hh : p.val < 628) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-624,by omega⟩
  have hp : (⟨624+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_156_small q

lemma step_check_chunk_157_small : ∀ p : Fin 4,
    stepCheck ⟨628+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_157 (p : Fin 929) (hl : 628 ≤ p.val) (hh : p.val < 632) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-628,by omega⟩
  have hp : (⟨628+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_157_small q

lemma step_check_chunk_158_small : ∀ p : Fin 4,
    stepCheck ⟨632+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_158 (p : Fin 929) (hl : 632 ≤ p.val) (hh : p.val < 636) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-632,by omega⟩
  have hp : (⟨632+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_158_small q

lemma step_check_chunk_159_small : ∀ p : Fin 4,
    stepCheck ⟨636+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_159 (p : Fin 929) (hl : 636 ≤ p.val) (hh : p.val < 640) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-636,by omega⟩
  have hp : (⟨636+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_159_small q

lemma step_check_chunk_160_small : ∀ p : Fin 4,
    stepCheck ⟨640+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_160 (p : Fin 929) (hl : 640 ≤ p.val) (hh : p.val < 644) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-640,by omega⟩
  have hp : (⟨640+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_160_small q

lemma step_check_chunk_161_small : ∀ p : Fin 4,
    stepCheck ⟨644+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_161 (p : Fin 929) (hl : 644 ≤ p.val) (hh : p.val < 648) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-644,by omega⟩
  have hp : (⟨644+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_161_small q

lemma step_check_chunk_162_small : ∀ p : Fin 4,
    stepCheck ⟨648+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_162 (p : Fin 929) (hl : 648 ≤ p.val) (hh : p.val < 652) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-648,by omega⟩
  have hp : (⟨648+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_162_small q

lemma step_check_chunk_163_small : ∀ p : Fin 4,
    stepCheck ⟨652+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_163 (p : Fin 929) (hl : 652 ≤ p.val) (hh : p.val < 656) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-652,by omega⟩
  have hp : (⟨652+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_163_small q

lemma step_check_chunk_164_small : ∀ p : Fin 4,
    stepCheck ⟨656+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_164 (p : Fin 929) (hl : 656 ≤ p.val) (hh : p.val < 660) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-656,by omega⟩
  have hp : (⟨656+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_164_small q

lemma step_check_chunk_165_small : ∀ p : Fin 4,
    stepCheck ⟨660+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_165 (p : Fin 929) (hl : 660 ≤ p.val) (hh : p.val < 664) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-660,by omega⟩
  have hp : (⟨660+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_165_small q

lemma step_check_chunk_166_small : ∀ p : Fin 4,
    stepCheck ⟨664+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_166 (p : Fin 929) (hl : 664 ≤ p.val) (hh : p.val < 668) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-664,by omega⟩
  have hp : (⟨664+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_166_small q

lemma step_check_chunk_167_small : ∀ p : Fin 4,
    stepCheck ⟨668+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_167 (p : Fin 929) (hl : 668 ≤ p.val) (hh : p.val < 672) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-668,by omega⟩
  have hp : (⟨668+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_167_small q

lemma step_check_chunk_168_small : ∀ p : Fin 4,
    stepCheck ⟨672+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_168 (p : Fin 929) (hl : 672 ≤ p.val) (hh : p.val < 676) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-672,by omega⟩
  have hp : (⟨672+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_168_small q

lemma step_check_chunk_169_small : ∀ p : Fin 4,
    stepCheck ⟨676+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_169 (p : Fin 929) (hl : 676 ≤ p.val) (hh : p.val < 680) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-676,by omega⟩
  have hp : (⟨676+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_169_small q

lemma step_check_chunk_170_small : ∀ p : Fin 4,
    stepCheck ⟨680+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_170 (p : Fin 929) (hl : 680 ≤ p.val) (hh : p.val < 684) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-680,by omega⟩
  have hp : (⟨680+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_170_small q

lemma step_check_chunk_171_small : ∀ p : Fin 4,
    stepCheck ⟨684+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_171 (p : Fin 929) (hl : 684 ≤ p.val) (hh : p.val < 688) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-684,by omega⟩
  have hp : (⟨684+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_171_small q

lemma step_check_chunk_172_small : ∀ p : Fin 4,
    stepCheck ⟨688+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_172 (p : Fin 929) (hl : 688 ≤ p.val) (hh : p.val < 692) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-688,by omega⟩
  have hp : (⟨688+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_172_small q

lemma step_check_chunk_173_small : ∀ p : Fin 4,
    stepCheck ⟨692+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_173 (p : Fin 929) (hl : 692 ≤ p.val) (hh : p.val < 696) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-692,by omega⟩
  have hp : (⟨692+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_173_small q

lemma step_check_chunk_174_small : ∀ p : Fin 4,
    stepCheck ⟨696+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_174 (p : Fin 929) (hl : 696 ≤ p.val) (hh : p.val < 700) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-696,by omega⟩
  have hp : (⟨696+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_174_small q

lemma step_check_chunk_175_small : ∀ p : Fin 4,
    stepCheck ⟨700+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_175 (p : Fin 929) (hl : 700 ≤ p.val) (hh : p.val < 704) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-700,by omega⟩
  have hp : (⟨700+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_175_small q

lemma step_check_chunk_176_small : ∀ p : Fin 4,
    stepCheck ⟨704+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_176 (p : Fin 929) (hl : 704 ≤ p.val) (hh : p.val < 708) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-704,by omega⟩
  have hp : (⟨704+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_176_small q

lemma step_check_chunk_177_small : ∀ p : Fin 4,
    stepCheck ⟨708+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_177 (p : Fin 929) (hl : 708 ≤ p.val) (hh : p.val < 712) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-708,by omega⟩
  have hp : (⟨708+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_177_small q

lemma step_check_chunk_178_small : ∀ p : Fin 4,
    stepCheck ⟨712+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_178 (p : Fin 929) (hl : 712 ≤ p.val) (hh : p.val < 716) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-712,by omega⟩
  have hp : (⟨712+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_178_small q

lemma step_check_chunk_179_small : ∀ p : Fin 4,
    stepCheck ⟨716+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_179 (p : Fin 929) (hl : 716 ≤ p.val) (hh : p.val < 720) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-716,by omega⟩
  have hp : (⟨716+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_179_small q

lemma step_check_chunk_180_small : ∀ p : Fin 4,
    stepCheck ⟨720+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_180 (p : Fin 929) (hl : 720 ≤ p.val) (hh : p.val < 724) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-720,by omega⟩
  have hp : (⟨720+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_180_small q

lemma step_check_chunk_181_small : ∀ p : Fin 4,
    stepCheck ⟨724+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_181 (p : Fin 929) (hl : 724 ≤ p.val) (hh : p.val < 728) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-724,by omega⟩
  have hp : (⟨724+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_181_small q

lemma step_check_chunk_182_small : ∀ p : Fin 4,
    stepCheck ⟨728+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_182 (p : Fin 929) (hl : 728 ≤ p.val) (hh : p.val < 732) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-728,by omega⟩
  have hp : (⟨728+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_182_small q

lemma step_check_chunk_183_small : ∀ p : Fin 4,
    stepCheck ⟨732+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_183 (p : Fin 929) (hl : 732 ≤ p.val) (hh : p.val < 736) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-732,by omega⟩
  have hp : (⟨732+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_183_small q

lemma step_check_chunk_184_small : ∀ p : Fin 4,
    stepCheck ⟨736+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_184 (p : Fin 929) (hl : 736 ≤ p.val) (hh : p.val < 740) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-736,by omega⟩
  have hp : (⟨736+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_184_small q

lemma step_check_chunk_185_small : ∀ p : Fin 4,
    stepCheck ⟨740+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_185 (p : Fin 929) (hl : 740 ≤ p.val) (hh : p.val < 744) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-740,by omega⟩
  have hp : (⟨740+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_185_small q

lemma step_check_chunk_186_small : ∀ p : Fin 4,
    stepCheck ⟨744+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_186 (p : Fin 929) (hl : 744 ≤ p.val) (hh : p.val < 748) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-744,by omega⟩
  have hp : (⟨744+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_186_small q

lemma step_check_chunk_187_small : ∀ p : Fin 4,
    stepCheck ⟨748+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_187 (p : Fin 929) (hl : 748 ≤ p.val) (hh : p.val < 752) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-748,by omega⟩
  have hp : (⟨748+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_187_small q

lemma step_check_chunk_188_small : ∀ p : Fin 4,
    stepCheck ⟨752+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_188 (p : Fin 929) (hl : 752 ≤ p.val) (hh : p.val < 756) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-752,by omega⟩
  have hp : (⟨752+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_188_small q

lemma step_check_chunk_189_small : ∀ p : Fin 4,
    stepCheck ⟨756+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_189 (p : Fin 929) (hl : 756 ≤ p.val) (hh : p.val < 760) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-756,by omega⟩
  have hp : (⟨756+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_189_small q

lemma step_check_chunk_190_small : ∀ p : Fin 4,
    stepCheck ⟨760+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_190 (p : Fin 929) (hl : 760 ≤ p.val) (hh : p.val < 764) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-760,by omega⟩
  have hp : (⟨760+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_190_small q

lemma step_check_chunk_191_small : ∀ p : Fin 4,
    stepCheck ⟨764+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_191 (p : Fin 929) (hl : 764 ≤ p.val) (hh : p.val < 768) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-764,by omega⟩
  have hp : (⟨764+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_191_small q

lemma step_check_chunk_192_small : ∀ p : Fin 4,
    stepCheck ⟨768+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_192 (p : Fin 929) (hl : 768 ≤ p.val) (hh : p.val < 772) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-768,by omega⟩
  have hp : (⟨768+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_192_small q

lemma step_check_chunk_193_small : ∀ p : Fin 4,
    stepCheck ⟨772+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_193 (p : Fin 929) (hl : 772 ≤ p.val) (hh : p.val < 776) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-772,by omega⟩
  have hp : (⟨772+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_193_small q

lemma step_check_chunk_194_small : ∀ p : Fin 4,
    stepCheck ⟨776+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_194 (p : Fin 929) (hl : 776 ≤ p.val) (hh : p.val < 780) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-776,by omega⟩
  have hp : (⟨776+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_194_small q

lemma step_check_chunk_195_small : ∀ p : Fin 4,
    stepCheck ⟨780+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_195 (p : Fin 929) (hl : 780 ≤ p.val) (hh : p.val < 784) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-780,by omega⟩
  have hp : (⟨780+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_195_small q

lemma step_check_chunk_196_small : ∀ p : Fin 4,
    stepCheck ⟨784+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_196 (p : Fin 929) (hl : 784 ≤ p.val) (hh : p.val < 788) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-784,by omega⟩
  have hp : (⟨784+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_196_small q

lemma step_check_chunk_197_small : ∀ p : Fin 4,
    stepCheck ⟨788+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_197 (p : Fin 929) (hl : 788 ≤ p.val) (hh : p.val < 792) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-788,by omega⟩
  have hp : (⟨788+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_197_small q

lemma step_check_chunk_198_small : ∀ p : Fin 4,
    stepCheck ⟨792+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_198 (p : Fin 929) (hl : 792 ≤ p.val) (hh : p.val < 796) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-792,by omega⟩
  have hp : (⟨792+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_198_small q

lemma step_check_chunk_199_small : ∀ p : Fin 4,
    stepCheck ⟨796+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_199 (p : Fin 929) (hl : 796 ≤ p.val) (hh : p.val < 800) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-796,by omega⟩
  have hp : (⟨796+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_199_small q

lemma step_check_chunk_200_small : ∀ p : Fin 4,
    stepCheck ⟨800+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_200 (p : Fin 929) (hl : 800 ≤ p.val) (hh : p.val < 804) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-800,by omega⟩
  have hp : (⟨800+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_200_small q

lemma step_check_chunk_201_small : ∀ p : Fin 4,
    stepCheck ⟨804+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_201 (p : Fin 929) (hl : 804 ≤ p.val) (hh : p.val < 808) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-804,by omega⟩
  have hp : (⟨804+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_201_small q

lemma step_check_chunk_202_small : ∀ p : Fin 4,
    stepCheck ⟨808+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_202 (p : Fin 929) (hl : 808 ≤ p.val) (hh : p.val < 812) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-808,by omega⟩
  have hp : (⟨808+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_202_small q

lemma step_check_chunk_203_small : ∀ p : Fin 4,
    stepCheck ⟨812+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_203 (p : Fin 929) (hl : 812 ≤ p.val) (hh : p.val < 816) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-812,by omega⟩
  have hp : (⟨812+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_203_small q

lemma step_check_chunk_204_small : ∀ p : Fin 4,
    stepCheck ⟨816+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_204 (p : Fin 929) (hl : 816 ≤ p.val) (hh : p.val < 820) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-816,by omega⟩
  have hp : (⟨816+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_204_small q

lemma step_check_chunk_205_small : ∀ p : Fin 4,
    stepCheck ⟨820+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_205 (p : Fin 929) (hl : 820 ≤ p.val) (hh : p.val < 824) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-820,by omega⟩
  have hp : (⟨820+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_205_small q

lemma step_check_chunk_206_small : ∀ p : Fin 4,
    stepCheck ⟨824+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_206 (p : Fin 929) (hl : 824 ≤ p.val) (hh : p.val < 828) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-824,by omega⟩
  have hp : (⟨824+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_206_small q

lemma step_check_chunk_207_small : ∀ p : Fin 4,
    stepCheck ⟨828+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_207 (p : Fin 929) (hl : 828 ≤ p.val) (hh : p.val < 832) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-828,by omega⟩
  have hp : (⟨828+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_207_small q

lemma step_check_chunk_208_small : ∀ p : Fin 4,
    stepCheck ⟨832+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_208 (p : Fin 929) (hl : 832 ≤ p.val) (hh : p.val < 836) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-832,by omega⟩
  have hp : (⟨832+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_208_small q

lemma step_check_chunk_209_small : ∀ p : Fin 4,
    stepCheck ⟨836+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_209 (p : Fin 929) (hl : 836 ≤ p.val) (hh : p.val < 840) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-836,by omega⟩
  have hp : (⟨836+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_209_small q

lemma step_check_chunk_210_small : ∀ p : Fin 4,
    stepCheck ⟨840+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_210 (p : Fin 929) (hl : 840 ≤ p.val) (hh : p.val < 844) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-840,by omega⟩
  have hp : (⟨840+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_210_small q

lemma step_check_chunk_211_small : ∀ p : Fin 4,
    stepCheck ⟨844+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_211 (p : Fin 929) (hl : 844 ≤ p.val) (hh : p.val < 848) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-844,by omega⟩
  have hp : (⟨844+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_211_small q

lemma step_check_chunk_212_small : ∀ p : Fin 4,
    stepCheck ⟨848+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_212 (p : Fin 929) (hl : 848 ≤ p.val) (hh : p.val < 852) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-848,by omega⟩
  have hp : (⟨848+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_212_small q

lemma step_check_chunk_213_small : ∀ p : Fin 4,
    stepCheck ⟨852+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_213 (p : Fin 929) (hl : 852 ≤ p.val) (hh : p.val < 856) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-852,by omega⟩
  have hp : (⟨852+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_213_small q

lemma step_check_chunk_214_small : ∀ p : Fin 4,
    stepCheck ⟨856+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_214 (p : Fin 929) (hl : 856 ≤ p.val) (hh : p.val < 860) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-856,by omega⟩
  have hp : (⟨856+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_214_small q

lemma step_check_chunk_215_small : ∀ p : Fin 4,
    stepCheck ⟨860+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_215 (p : Fin 929) (hl : 860 ≤ p.val) (hh : p.val < 864) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-860,by omega⟩
  have hp : (⟨860+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_215_small q

lemma step_check_chunk_216_small : ∀ p : Fin 4,
    stepCheck ⟨864+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_216 (p : Fin 929) (hl : 864 ≤ p.val) (hh : p.val < 868) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-864,by omega⟩
  have hp : (⟨864+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_216_small q

lemma step_check_chunk_217_small : ∀ p : Fin 4,
    stepCheck ⟨868+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_217 (p : Fin 929) (hl : 868 ≤ p.val) (hh : p.val < 872) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-868,by omega⟩
  have hp : (⟨868+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_217_small q

lemma step_check_chunk_218_small : ∀ p : Fin 4,
    stepCheck ⟨872+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_218 (p : Fin 929) (hl : 872 ≤ p.val) (hh : p.val < 876) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-872,by omega⟩
  have hp : (⟨872+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_218_small q

lemma step_check_chunk_219_small : ∀ p : Fin 4,
    stepCheck ⟨876+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_219 (p : Fin 929) (hl : 876 ≤ p.val) (hh : p.val < 880) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-876,by omega⟩
  have hp : (⟨876+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_219_small q

lemma step_check_chunk_220_small : ∀ p : Fin 4,
    stepCheck ⟨880+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_220 (p : Fin 929) (hl : 880 ≤ p.val) (hh : p.val < 884) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-880,by omega⟩
  have hp : (⟨880+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_220_small q

lemma step_check_chunk_221_small : ∀ p : Fin 4,
    stepCheck ⟨884+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_221 (p : Fin 929) (hl : 884 ≤ p.val) (hh : p.val < 888) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-884,by omega⟩
  have hp : (⟨884+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_221_small q

lemma step_check_chunk_222_small : ∀ p : Fin 4,
    stepCheck ⟨888+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_222 (p : Fin 929) (hl : 888 ≤ p.val) (hh : p.val < 892) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-888,by omega⟩
  have hp : (⟨888+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_222_small q

lemma step_check_chunk_223_small : ∀ p : Fin 4,
    stepCheck ⟨892+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_223 (p : Fin 929) (hl : 892 ≤ p.val) (hh : p.val < 896) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-892,by omega⟩
  have hp : (⟨892+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_223_small q

lemma step_check_chunk_224_small : ∀ p : Fin 4,
    stepCheck ⟨896+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_224 (p : Fin 929) (hl : 896 ≤ p.val) (hh : p.val < 900) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-896,by omega⟩
  have hp : (⟨896+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_224_small q

lemma step_check_chunk_225_small : ∀ p : Fin 4,
    stepCheck ⟨900+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_225 (p : Fin 929) (hl : 900 ≤ p.val) (hh : p.val < 904) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-900,by omega⟩
  have hp : (⟨900+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_225_small q

lemma step_check_chunk_226_small : ∀ p : Fin 4,
    stepCheck ⟨904+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_226 (p : Fin 929) (hl : 904 ≤ p.val) (hh : p.val < 908) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-904,by omega⟩
  have hp : (⟨904+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_226_small q

lemma step_check_chunk_227_small : ∀ p : Fin 4,
    stepCheck ⟨908+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_227 (p : Fin 929) (hl : 908 ≤ p.val) (hh : p.val < 912) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-908,by omega⟩
  have hp : (⟨908+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_227_small q

lemma step_check_chunk_228_small : ∀ p : Fin 4,
    stepCheck ⟨912+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_228 (p : Fin 929) (hl : 912 ≤ p.val) (hh : p.val < 916) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-912,by omega⟩
  have hp : (⟨912+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_228_small q

lemma step_check_chunk_229_small : ∀ p : Fin 4,
    stepCheck ⟨916+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_229 (p : Fin 929) (hl : 916 ≤ p.val) (hh : p.val < 920) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-916,by omega⟩
  have hp : (⟨916+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_229_small q

lemma step_check_chunk_230_small : ∀ p : Fin 4,
    stepCheck ⟨920+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_230 (p : Fin 929) (hl : 920 ≤ p.val) (hh : p.val < 924) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-920,by omega⟩
  have hp : (⟨920+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_230_small q

lemma step_check_chunk_231_small : ∀ p : Fin 4,
    stepCheck ⟨924+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_231 (p : Fin 929) (hl : 924 ≤ p.val) (hh : p.val < 928) : stepCheck p = true := by
  let q : Fin 4 := ⟨p.val-924,by omega⟩
  have hp : (⟨924+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_231_small q

lemma step_check_chunk_232_small : ∀ p : Fin 1,
    stepCheck ⟨928+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma step_check_chunk_232 (p : Fin 929) (hl : 928 ≤ p.val) (hh : p.val < 929) : stepCheck p = true := by
  let q : Fin 1 := ⟨p.val-928,by omega⟩
  have hp : (⟨928+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using step_check_chunk_232_small q

lemma step_check_all (p : Fin 929) : stepCheck p = true := by
  have hlo_root : 0 ≤ p.val := Nat.zero_le _
  have hhi_root : p.val < 929 := p.isLt
  by_cases hmid_0_233 : p.val < 464
  · by_cases hmid_0_116 : p.val < 232
    · by_cases hmid_0_58 : p.val < 116
      · by_cases hmid_0_29 : p.val < 56
        · by_cases hmid_0_14 : p.val < 28
          · by_cases hmid_0_7 : p.val < 12
            · by_cases hmid_0_3 : p.val < 4
              · exact step_check_chunk_0 p hlo_root hmid_0_3
              · have hlo_1_3 : 4 ≤ p.val := Nat.le_of_not_gt hmid_0_3
                by_cases hmid_1_3 : p.val < 8
                · exact step_check_chunk_1 p hlo_1_3 hmid_1_3
                · have hlo_2_3 : 8 ≤ p.val := Nat.le_of_not_gt hmid_1_3
                  exact step_check_chunk_2 p hlo_2_3 hmid_0_7
            · have hlo_3_7 : 12 ≤ p.val := Nat.le_of_not_gt hmid_0_7
              by_cases hmid_3_7 : p.val < 20
              · by_cases hmid_3_5 : p.val < 16
                · exact step_check_chunk_3 p hlo_3_7 hmid_3_5
                · have hlo_4_5 : 16 ≤ p.val := Nat.le_of_not_gt hmid_3_5
                  exact step_check_chunk_4 p hlo_4_5 hmid_3_7
              · have hlo_5_7 : 20 ≤ p.val := Nat.le_of_not_gt hmid_3_7
                by_cases hmid_5_7 : p.val < 24
                · exact step_check_chunk_5 p hlo_5_7 hmid_5_7
                · have hlo_6_7 : 24 ≤ p.val := Nat.le_of_not_gt hmid_5_7
                  exact step_check_chunk_6 p hlo_6_7 hmid_0_14
          · have hlo_7_14 : 28 ≤ p.val := Nat.le_of_not_gt hmid_0_14
            by_cases hmid_7_14 : p.val < 40
            · by_cases hmid_7_10 : p.val < 32
              · exact step_check_chunk_7 p hlo_7_14 hmid_7_10
              · have hlo_8_10 : 32 ≤ p.val := Nat.le_of_not_gt hmid_7_10
                by_cases hmid_8_10 : p.val < 36
                · exact step_check_chunk_8 p hlo_8_10 hmid_8_10
                · have hlo_9_10 : 36 ≤ p.val := Nat.le_of_not_gt hmid_8_10
                  exact step_check_chunk_9 p hlo_9_10 hmid_7_14
            · have hlo_10_14 : 40 ≤ p.val := Nat.le_of_not_gt hmid_7_14
              by_cases hmid_10_14 : p.val < 48
              · by_cases hmid_10_12 : p.val < 44
                · exact step_check_chunk_10 p hlo_10_14 hmid_10_12
                · have hlo_11_12 : 44 ≤ p.val := Nat.le_of_not_gt hmid_10_12
                  exact step_check_chunk_11 p hlo_11_12 hmid_10_14
              · have hlo_12_14 : 48 ≤ p.val := Nat.le_of_not_gt hmid_10_14
                by_cases hmid_12_14 : p.val < 52
                · exact step_check_chunk_12 p hlo_12_14 hmid_12_14
                · have hlo_13_14 : 52 ≤ p.val := Nat.le_of_not_gt hmid_12_14
                  exact step_check_chunk_13 p hlo_13_14 hmid_0_29
        · have hlo_14_29 : 56 ≤ p.val := Nat.le_of_not_gt hmid_0_29
          by_cases hmid_14_29 : p.val < 84
          · by_cases hmid_14_21 : p.val < 68
            · by_cases hmid_14_17 : p.val < 60
              · exact step_check_chunk_14 p hlo_14_29 hmid_14_17
              · have hlo_15_17 : 60 ≤ p.val := Nat.le_of_not_gt hmid_14_17
                by_cases hmid_15_17 : p.val < 64
                · exact step_check_chunk_15 p hlo_15_17 hmid_15_17
                · have hlo_16_17 : 64 ≤ p.val := Nat.le_of_not_gt hmid_15_17
                  exact step_check_chunk_16 p hlo_16_17 hmid_14_21
            · have hlo_17_21 : 68 ≤ p.val := Nat.le_of_not_gt hmid_14_21
              by_cases hmid_17_21 : p.val < 76
              · by_cases hmid_17_19 : p.val < 72
                · exact step_check_chunk_17 p hlo_17_21 hmid_17_19
                · have hlo_18_19 : 72 ≤ p.val := Nat.le_of_not_gt hmid_17_19
                  exact step_check_chunk_18 p hlo_18_19 hmid_17_21
              · have hlo_19_21 : 76 ≤ p.val := Nat.le_of_not_gt hmid_17_21
                by_cases hmid_19_21 : p.val < 80
                · exact step_check_chunk_19 p hlo_19_21 hmid_19_21
                · have hlo_20_21 : 80 ≤ p.val := Nat.le_of_not_gt hmid_19_21
                  exact step_check_chunk_20 p hlo_20_21 hmid_14_29
          · have hlo_21_29 : 84 ≤ p.val := Nat.le_of_not_gt hmid_14_29
            by_cases hmid_21_29 : p.val < 100
            · by_cases hmid_21_25 : p.val < 92
              · by_cases hmid_21_23 : p.val < 88
                · exact step_check_chunk_21 p hlo_21_29 hmid_21_23
                · have hlo_22_23 : 88 ≤ p.val := Nat.le_of_not_gt hmid_21_23
                  exact step_check_chunk_22 p hlo_22_23 hmid_21_25
              · have hlo_23_25 : 92 ≤ p.val := Nat.le_of_not_gt hmid_21_25
                by_cases hmid_23_25 : p.val < 96
                · exact step_check_chunk_23 p hlo_23_25 hmid_23_25
                · have hlo_24_25 : 96 ≤ p.val := Nat.le_of_not_gt hmid_23_25
                  exact step_check_chunk_24 p hlo_24_25 hmid_21_29
            · have hlo_25_29 : 100 ≤ p.val := Nat.le_of_not_gt hmid_21_29
              by_cases hmid_25_29 : p.val < 108
              · by_cases hmid_25_27 : p.val < 104
                · exact step_check_chunk_25 p hlo_25_29 hmid_25_27
                · have hlo_26_27 : 104 ≤ p.val := Nat.le_of_not_gt hmid_25_27
                  exact step_check_chunk_26 p hlo_26_27 hmid_25_29
              · have hlo_27_29 : 108 ≤ p.val := Nat.le_of_not_gt hmid_25_29
                by_cases hmid_27_29 : p.val < 112
                · exact step_check_chunk_27 p hlo_27_29 hmid_27_29
                · have hlo_28_29 : 112 ≤ p.val := Nat.le_of_not_gt hmid_27_29
                  exact step_check_chunk_28 p hlo_28_29 hmid_0_58
      · have hlo_29_58 : 116 ≤ p.val := Nat.le_of_not_gt hmid_0_58
        by_cases hmid_29_58 : p.val < 172
        · by_cases hmid_29_43 : p.val < 144
          · by_cases hmid_29_36 : p.val < 128
            · by_cases hmid_29_32 : p.val < 120
              · exact step_check_chunk_29 p hlo_29_58 hmid_29_32
              · have hlo_30_32 : 120 ≤ p.val := Nat.le_of_not_gt hmid_29_32
                by_cases hmid_30_32 : p.val < 124
                · exact step_check_chunk_30 p hlo_30_32 hmid_30_32
                · have hlo_31_32 : 124 ≤ p.val := Nat.le_of_not_gt hmid_30_32
                  exact step_check_chunk_31 p hlo_31_32 hmid_29_36
            · have hlo_32_36 : 128 ≤ p.val := Nat.le_of_not_gt hmid_29_36
              by_cases hmid_32_36 : p.val < 136
              · by_cases hmid_32_34 : p.val < 132
                · exact step_check_chunk_32 p hlo_32_36 hmid_32_34
                · have hlo_33_34 : 132 ≤ p.val := Nat.le_of_not_gt hmid_32_34
                  exact step_check_chunk_33 p hlo_33_34 hmid_32_36
              · have hlo_34_36 : 136 ≤ p.val := Nat.le_of_not_gt hmid_32_36
                by_cases hmid_34_36 : p.val < 140
                · exact step_check_chunk_34 p hlo_34_36 hmid_34_36
                · have hlo_35_36 : 140 ≤ p.val := Nat.le_of_not_gt hmid_34_36
                  exact step_check_chunk_35 p hlo_35_36 hmid_29_43
          · have hlo_36_43 : 144 ≤ p.val := Nat.le_of_not_gt hmid_29_43
            by_cases hmid_36_43 : p.val < 156
            · by_cases hmid_36_39 : p.val < 148
              · exact step_check_chunk_36 p hlo_36_43 hmid_36_39
              · have hlo_37_39 : 148 ≤ p.val := Nat.le_of_not_gt hmid_36_39
                by_cases hmid_37_39 : p.val < 152
                · exact step_check_chunk_37 p hlo_37_39 hmid_37_39
                · have hlo_38_39 : 152 ≤ p.val := Nat.le_of_not_gt hmid_37_39
                  exact step_check_chunk_38 p hlo_38_39 hmid_36_43
            · have hlo_39_43 : 156 ≤ p.val := Nat.le_of_not_gt hmid_36_43
              by_cases hmid_39_43 : p.val < 164
              · by_cases hmid_39_41 : p.val < 160
                · exact step_check_chunk_39 p hlo_39_43 hmid_39_41
                · have hlo_40_41 : 160 ≤ p.val := Nat.le_of_not_gt hmid_39_41
                  exact step_check_chunk_40 p hlo_40_41 hmid_39_43
              · have hlo_41_43 : 164 ≤ p.val := Nat.le_of_not_gt hmid_39_43
                by_cases hmid_41_43 : p.val < 168
                · exact step_check_chunk_41 p hlo_41_43 hmid_41_43
                · have hlo_42_43 : 168 ≤ p.val := Nat.le_of_not_gt hmid_41_43
                  exact step_check_chunk_42 p hlo_42_43 hmid_29_58
        · have hlo_43_58 : 172 ≤ p.val := Nat.le_of_not_gt hmid_29_58
          by_cases hmid_43_58 : p.val < 200
          · by_cases hmid_43_50 : p.val < 184
            · by_cases hmid_43_46 : p.val < 176
              · exact step_check_chunk_43 p hlo_43_58 hmid_43_46
              · have hlo_44_46 : 176 ≤ p.val := Nat.le_of_not_gt hmid_43_46
                by_cases hmid_44_46 : p.val < 180
                · exact step_check_chunk_44 p hlo_44_46 hmid_44_46
                · have hlo_45_46 : 180 ≤ p.val := Nat.le_of_not_gt hmid_44_46
                  exact step_check_chunk_45 p hlo_45_46 hmid_43_50
            · have hlo_46_50 : 184 ≤ p.val := Nat.le_of_not_gt hmid_43_50
              by_cases hmid_46_50 : p.val < 192
              · by_cases hmid_46_48 : p.val < 188
                · exact step_check_chunk_46 p hlo_46_50 hmid_46_48
                · have hlo_47_48 : 188 ≤ p.val := Nat.le_of_not_gt hmid_46_48
                  exact step_check_chunk_47 p hlo_47_48 hmid_46_50
              · have hlo_48_50 : 192 ≤ p.val := Nat.le_of_not_gt hmid_46_50
                by_cases hmid_48_50 : p.val < 196
                · exact step_check_chunk_48 p hlo_48_50 hmid_48_50
                · have hlo_49_50 : 196 ≤ p.val := Nat.le_of_not_gt hmid_48_50
                  exact step_check_chunk_49 p hlo_49_50 hmid_43_58
          · have hlo_50_58 : 200 ≤ p.val := Nat.le_of_not_gt hmid_43_58
            by_cases hmid_50_58 : p.val < 216
            · by_cases hmid_50_54 : p.val < 208
              · by_cases hmid_50_52 : p.val < 204
                · exact step_check_chunk_50 p hlo_50_58 hmid_50_52
                · have hlo_51_52 : 204 ≤ p.val := Nat.le_of_not_gt hmid_50_52
                  exact step_check_chunk_51 p hlo_51_52 hmid_50_54
              · have hlo_52_54 : 208 ≤ p.val := Nat.le_of_not_gt hmid_50_54
                by_cases hmid_52_54 : p.val < 212
                · exact step_check_chunk_52 p hlo_52_54 hmid_52_54
                · have hlo_53_54 : 212 ≤ p.val := Nat.le_of_not_gt hmid_52_54
                  exact step_check_chunk_53 p hlo_53_54 hmid_50_58
            · have hlo_54_58 : 216 ≤ p.val := Nat.le_of_not_gt hmid_50_58
              by_cases hmid_54_58 : p.val < 224
              · by_cases hmid_54_56 : p.val < 220
                · exact step_check_chunk_54 p hlo_54_58 hmid_54_56
                · have hlo_55_56 : 220 ≤ p.val := Nat.le_of_not_gt hmid_54_56
                  exact step_check_chunk_55 p hlo_55_56 hmid_54_58
              · have hlo_56_58 : 224 ≤ p.val := Nat.le_of_not_gt hmid_54_58
                by_cases hmid_56_58 : p.val < 228
                · exact step_check_chunk_56 p hlo_56_58 hmid_56_58
                · have hlo_57_58 : 228 ≤ p.val := Nat.le_of_not_gt hmid_56_58
                  exact step_check_chunk_57 p hlo_57_58 hmid_0_116
    · have hlo_58_116 : 232 ≤ p.val := Nat.le_of_not_gt hmid_0_116
      by_cases hmid_58_116 : p.val < 348
      · by_cases hmid_58_87 : p.val < 288
        · by_cases hmid_58_72 : p.val < 260
          · by_cases hmid_58_65 : p.val < 244
            · by_cases hmid_58_61 : p.val < 236
              · exact step_check_chunk_58 p hlo_58_116 hmid_58_61
              · have hlo_59_61 : 236 ≤ p.val := Nat.le_of_not_gt hmid_58_61
                by_cases hmid_59_61 : p.val < 240
                · exact step_check_chunk_59 p hlo_59_61 hmid_59_61
                · have hlo_60_61 : 240 ≤ p.val := Nat.le_of_not_gt hmid_59_61
                  exact step_check_chunk_60 p hlo_60_61 hmid_58_65
            · have hlo_61_65 : 244 ≤ p.val := Nat.le_of_not_gt hmid_58_65
              by_cases hmid_61_65 : p.val < 252
              · by_cases hmid_61_63 : p.val < 248
                · exact step_check_chunk_61 p hlo_61_65 hmid_61_63
                · have hlo_62_63 : 248 ≤ p.val := Nat.le_of_not_gt hmid_61_63
                  exact step_check_chunk_62 p hlo_62_63 hmid_61_65
              · have hlo_63_65 : 252 ≤ p.val := Nat.le_of_not_gt hmid_61_65
                by_cases hmid_63_65 : p.val < 256
                · exact step_check_chunk_63 p hlo_63_65 hmid_63_65
                · have hlo_64_65 : 256 ≤ p.val := Nat.le_of_not_gt hmid_63_65
                  exact step_check_chunk_64 p hlo_64_65 hmid_58_72
          · have hlo_65_72 : 260 ≤ p.val := Nat.le_of_not_gt hmid_58_72
            by_cases hmid_65_72 : p.val < 272
            · by_cases hmid_65_68 : p.val < 264
              · exact step_check_chunk_65 p hlo_65_72 hmid_65_68
              · have hlo_66_68 : 264 ≤ p.val := Nat.le_of_not_gt hmid_65_68
                by_cases hmid_66_68 : p.val < 268
                · exact step_check_chunk_66 p hlo_66_68 hmid_66_68
                · have hlo_67_68 : 268 ≤ p.val := Nat.le_of_not_gt hmid_66_68
                  exact step_check_chunk_67 p hlo_67_68 hmid_65_72
            · have hlo_68_72 : 272 ≤ p.val := Nat.le_of_not_gt hmid_65_72
              by_cases hmid_68_72 : p.val < 280
              · by_cases hmid_68_70 : p.val < 276
                · exact step_check_chunk_68 p hlo_68_72 hmid_68_70
                · have hlo_69_70 : 276 ≤ p.val := Nat.le_of_not_gt hmid_68_70
                  exact step_check_chunk_69 p hlo_69_70 hmid_68_72
              · have hlo_70_72 : 280 ≤ p.val := Nat.le_of_not_gt hmid_68_72
                by_cases hmid_70_72 : p.val < 284
                · exact step_check_chunk_70 p hlo_70_72 hmid_70_72
                · have hlo_71_72 : 284 ≤ p.val := Nat.le_of_not_gt hmid_70_72
                  exact step_check_chunk_71 p hlo_71_72 hmid_58_87
        · have hlo_72_87 : 288 ≤ p.val := Nat.le_of_not_gt hmid_58_87
          by_cases hmid_72_87 : p.val < 316
          · by_cases hmid_72_79 : p.val < 300
            · by_cases hmid_72_75 : p.val < 292
              · exact step_check_chunk_72 p hlo_72_87 hmid_72_75
              · have hlo_73_75 : 292 ≤ p.val := Nat.le_of_not_gt hmid_72_75
                by_cases hmid_73_75 : p.val < 296
                · exact step_check_chunk_73 p hlo_73_75 hmid_73_75
                · have hlo_74_75 : 296 ≤ p.val := Nat.le_of_not_gt hmid_73_75
                  exact step_check_chunk_74 p hlo_74_75 hmid_72_79
            · have hlo_75_79 : 300 ≤ p.val := Nat.le_of_not_gt hmid_72_79
              by_cases hmid_75_79 : p.val < 308
              · by_cases hmid_75_77 : p.val < 304
                · exact step_check_chunk_75 p hlo_75_79 hmid_75_77
                · have hlo_76_77 : 304 ≤ p.val := Nat.le_of_not_gt hmid_75_77
                  exact step_check_chunk_76 p hlo_76_77 hmid_75_79
              · have hlo_77_79 : 308 ≤ p.val := Nat.le_of_not_gt hmid_75_79
                by_cases hmid_77_79 : p.val < 312
                · exact step_check_chunk_77 p hlo_77_79 hmid_77_79
                · have hlo_78_79 : 312 ≤ p.val := Nat.le_of_not_gt hmid_77_79
                  exact step_check_chunk_78 p hlo_78_79 hmid_72_87
          · have hlo_79_87 : 316 ≤ p.val := Nat.le_of_not_gt hmid_72_87
            by_cases hmid_79_87 : p.val < 332
            · by_cases hmid_79_83 : p.val < 324
              · by_cases hmid_79_81 : p.val < 320
                · exact step_check_chunk_79 p hlo_79_87 hmid_79_81
                · have hlo_80_81 : 320 ≤ p.val := Nat.le_of_not_gt hmid_79_81
                  exact step_check_chunk_80 p hlo_80_81 hmid_79_83
              · have hlo_81_83 : 324 ≤ p.val := Nat.le_of_not_gt hmid_79_83
                by_cases hmid_81_83 : p.val < 328
                · exact step_check_chunk_81 p hlo_81_83 hmid_81_83
                · have hlo_82_83 : 328 ≤ p.val := Nat.le_of_not_gt hmid_81_83
                  exact step_check_chunk_82 p hlo_82_83 hmid_79_87
            · have hlo_83_87 : 332 ≤ p.val := Nat.le_of_not_gt hmid_79_87
              by_cases hmid_83_87 : p.val < 340
              · by_cases hmid_83_85 : p.val < 336
                · exact step_check_chunk_83 p hlo_83_87 hmid_83_85
                · have hlo_84_85 : 336 ≤ p.val := Nat.le_of_not_gt hmid_83_85
                  exact step_check_chunk_84 p hlo_84_85 hmid_83_87
              · have hlo_85_87 : 340 ≤ p.val := Nat.le_of_not_gt hmid_83_87
                by_cases hmid_85_87 : p.val < 344
                · exact step_check_chunk_85 p hlo_85_87 hmid_85_87
                · have hlo_86_87 : 344 ≤ p.val := Nat.le_of_not_gt hmid_85_87
                  exact step_check_chunk_86 p hlo_86_87 hmid_58_116
      · have hlo_87_116 : 348 ≤ p.val := Nat.le_of_not_gt hmid_58_116
        by_cases hmid_87_116 : p.val < 404
        · by_cases hmid_87_101 : p.val < 376
          · by_cases hmid_87_94 : p.val < 360
            · by_cases hmid_87_90 : p.val < 352
              · exact step_check_chunk_87 p hlo_87_116 hmid_87_90
              · have hlo_88_90 : 352 ≤ p.val := Nat.le_of_not_gt hmid_87_90
                by_cases hmid_88_90 : p.val < 356
                · exact step_check_chunk_88 p hlo_88_90 hmid_88_90
                · have hlo_89_90 : 356 ≤ p.val := Nat.le_of_not_gt hmid_88_90
                  exact step_check_chunk_89 p hlo_89_90 hmid_87_94
            · have hlo_90_94 : 360 ≤ p.val := Nat.le_of_not_gt hmid_87_94
              by_cases hmid_90_94 : p.val < 368
              · by_cases hmid_90_92 : p.val < 364
                · exact step_check_chunk_90 p hlo_90_94 hmid_90_92
                · have hlo_91_92 : 364 ≤ p.val := Nat.le_of_not_gt hmid_90_92
                  exact step_check_chunk_91 p hlo_91_92 hmid_90_94
              · have hlo_92_94 : 368 ≤ p.val := Nat.le_of_not_gt hmid_90_94
                by_cases hmid_92_94 : p.val < 372
                · exact step_check_chunk_92 p hlo_92_94 hmid_92_94
                · have hlo_93_94 : 372 ≤ p.val := Nat.le_of_not_gt hmid_92_94
                  exact step_check_chunk_93 p hlo_93_94 hmid_87_101
          · have hlo_94_101 : 376 ≤ p.val := Nat.le_of_not_gt hmid_87_101
            by_cases hmid_94_101 : p.val < 388
            · by_cases hmid_94_97 : p.val < 380
              · exact step_check_chunk_94 p hlo_94_101 hmid_94_97
              · have hlo_95_97 : 380 ≤ p.val := Nat.le_of_not_gt hmid_94_97
                by_cases hmid_95_97 : p.val < 384
                · exact step_check_chunk_95 p hlo_95_97 hmid_95_97
                · have hlo_96_97 : 384 ≤ p.val := Nat.le_of_not_gt hmid_95_97
                  exact step_check_chunk_96 p hlo_96_97 hmid_94_101
            · have hlo_97_101 : 388 ≤ p.val := Nat.le_of_not_gt hmid_94_101
              by_cases hmid_97_101 : p.val < 396
              · by_cases hmid_97_99 : p.val < 392
                · exact step_check_chunk_97 p hlo_97_101 hmid_97_99
                · have hlo_98_99 : 392 ≤ p.val := Nat.le_of_not_gt hmid_97_99
                  exact step_check_chunk_98 p hlo_98_99 hmid_97_101
              · have hlo_99_101 : 396 ≤ p.val := Nat.le_of_not_gt hmid_97_101
                by_cases hmid_99_101 : p.val < 400
                · exact step_check_chunk_99 p hlo_99_101 hmid_99_101
                · have hlo_100_101 : 400 ≤ p.val := Nat.le_of_not_gt hmid_99_101
                  exact step_check_chunk_100 p hlo_100_101 hmid_87_116
        · have hlo_101_116 : 404 ≤ p.val := Nat.le_of_not_gt hmid_87_116
          by_cases hmid_101_116 : p.val < 432
          · by_cases hmid_101_108 : p.val < 416
            · by_cases hmid_101_104 : p.val < 408
              · exact step_check_chunk_101 p hlo_101_116 hmid_101_104
              · have hlo_102_104 : 408 ≤ p.val := Nat.le_of_not_gt hmid_101_104
                by_cases hmid_102_104 : p.val < 412
                · exact step_check_chunk_102 p hlo_102_104 hmid_102_104
                · have hlo_103_104 : 412 ≤ p.val := Nat.le_of_not_gt hmid_102_104
                  exact step_check_chunk_103 p hlo_103_104 hmid_101_108
            · have hlo_104_108 : 416 ≤ p.val := Nat.le_of_not_gt hmid_101_108
              by_cases hmid_104_108 : p.val < 424
              · by_cases hmid_104_106 : p.val < 420
                · exact step_check_chunk_104 p hlo_104_108 hmid_104_106
                · have hlo_105_106 : 420 ≤ p.val := Nat.le_of_not_gt hmid_104_106
                  exact step_check_chunk_105 p hlo_105_106 hmid_104_108
              · have hlo_106_108 : 424 ≤ p.val := Nat.le_of_not_gt hmid_104_108
                by_cases hmid_106_108 : p.val < 428
                · exact step_check_chunk_106 p hlo_106_108 hmid_106_108
                · have hlo_107_108 : 428 ≤ p.val := Nat.le_of_not_gt hmid_106_108
                  exact step_check_chunk_107 p hlo_107_108 hmid_101_116
          · have hlo_108_116 : 432 ≤ p.val := Nat.le_of_not_gt hmid_101_116
            by_cases hmid_108_116 : p.val < 448
            · by_cases hmid_108_112 : p.val < 440
              · by_cases hmid_108_110 : p.val < 436
                · exact step_check_chunk_108 p hlo_108_116 hmid_108_110
                · have hlo_109_110 : 436 ≤ p.val := Nat.le_of_not_gt hmid_108_110
                  exact step_check_chunk_109 p hlo_109_110 hmid_108_112
              · have hlo_110_112 : 440 ≤ p.val := Nat.le_of_not_gt hmid_108_112
                by_cases hmid_110_112 : p.val < 444
                · exact step_check_chunk_110 p hlo_110_112 hmid_110_112
                · have hlo_111_112 : 444 ≤ p.val := Nat.le_of_not_gt hmid_110_112
                  exact step_check_chunk_111 p hlo_111_112 hmid_108_116
            · have hlo_112_116 : 448 ≤ p.val := Nat.le_of_not_gt hmid_108_116
              by_cases hmid_112_116 : p.val < 456
              · by_cases hmid_112_114 : p.val < 452
                · exact step_check_chunk_112 p hlo_112_116 hmid_112_114
                · have hlo_113_114 : 452 ≤ p.val := Nat.le_of_not_gt hmid_112_114
                  exact step_check_chunk_113 p hlo_113_114 hmid_112_116
              · have hlo_114_116 : 456 ≤ p.val := Nat.le_of_not_gt hmid_112_116
                by_cases hmid_114_116 : p.val < 460
                · exact step_check_chunk_114 p hlo_114_116 hmid_114_116
                · have hlo_115_116 : 460 ≤ p.val := Nat.le_of_not_gt hmid_114_116
                  exact step_check_chunk_115 p hlo_115_116 hmid_0_233
  · have hlo_116_233 : 464 ≤ p.val := Nat.le_of_not_gt hmid_0_233
    by_cases hmid_116_233 : p.val < 696
    · by_cases hmid_116_174 : p.val < 580
      · by_cases hmid_116_145 : p.val < 520
        · by_cases hmid_116_130 : p.val < 492
          · by_cases hmid_116_123 : p.val < 476
            · by_cases hmid_116_119 : p.val < 468
              · exact step_check_chunk_116 p hlo_116_233 hmid_116_119
              · have hlo_117_119 : 468 ≤ p.val := Nat.le_of_not_gt hmid_116_119
                by_cases hmid_117_119 : p.val < 472
                · exact step_check_chunk_117 p hlo_117_119 hmid_117_119
                · have hlo_118_119 : 472 ≤ p.val := Nat.le_of_not_gt hmid_117_119
                  exact step_check_chunk_118 p hlo_118_119 hmid_116_123
            · have hlo_119_123 : 476 ≤ p.val := Nat.le_of_not_gt hmid_116_123
              by_cases hmid_119_123 : p.val < 484
              · by_cases hmid_119_121 : p.val < 480
                · exact step_check_chunk_119 p hlo_119_123 hmid_119_121
                · have hlo_120_121 : 480 ≤ p.val := Nat.le_of_not_gt hmid_119_121
                  exact step_check_chunk_120 p hlo_120_121 hmid_119_123
              · have hlo_121_123 : 484 ≤ p.val := Nat.le_of_not_gt hmid_119_123
                by_cases hmid_121_123 : p.val < 488
                · exact step_check_chunk_121 p hlo_121_123 hmid_121_123
                · have hlo_122_123 : 488 ≤ p.val := Nat.le_of_not_gt hmid_121_123
                  exact step_check_chunk_122 p hlo_122_123 hmid_116_130
          · have hlo_123_130 : 492 ≤ p.val := Nat.le_of_not_gt hmid_116_130
            by_cases hmid_123_130 : p.val < 504
            · by_cases hmid_123_126 : p.val < 496
              · exact step_check_chunk_123 p hlo_123_130 hmid_123_126
              · have hlo_124_126 : 496 ≤ p.val := Nat.le_of_not_gt hmid_123_126
                by_cases hmid_124_126 : p.val < 500
                · exact step_check_chunk_124 p hlo_124_126 hmid_124_126
                · have hlo_125_126 : 500 ≤ p.val := Nat.le_of_not_gt hmid_124_126
                  exact step_check_chunk_125 p hlo_125_126 hmid_123_130
            · have hlo_126_130 : 504 ≤ p.val := Nat.le_of_not_gt hmid_123_130
              by_cases hmid_126_130 : p.val < 512
              · by_cases hmid_126_128 : p.val < 508
                · exact step_check_chunk_126 p hlo_126_130 hmid_126_128
                · have hlo_127_128 : 508 ≤ p.val := Nat.le_of_not_gt hmid_126_128
                  exact step_check_chunk_127 p hlo_127_128 hmid_126_130
              · have hlo_128_130 : 512 ≤ p.val := Nat.le_of_not_gt hmid_126_130
                by_cases hmid_128_130 : p.val < 516
                · exact step_check_chunk_128 p hlo_128_130 hmid_128_130
                · have hlo_129_130 : 516 ≤ p.val := Nat.le_of_not_gt hmid_128_130
                  exact step_check_chunk_129 p hlo_129_130 hmid_116_145
        · have hlo_130_145 : 520 ≤ p.val := Nat.le_of_not_gt hmid_116_145
          by_cases hmid_130_145 : p.val < 548
          · by_cases hmid_130_137 : p.val < 532
            · by_cases hmid_130_133 : p.val < 524
              · exact step_check_chunk_130 p hlo_130_145 hmid_130_133
              · have hlo_131_133 : 524 ≤ p.val := Nat.le_of_not_gt hmid_130_133
                by_cases hmid_131_133 : p.val < 528
                · exact step_check_chunk_131 p hlo_131_133 hmid_131_133
                · have hlo_132_133 : 528 ≤ p.val := Nat.le_of_not_gt hmid_131_133
                  exact step_check_chunk_132 p hlo_132_133 hmid_130_137
            · have hlo_133_137 : 532 ≤ p.val := Nat.le_of_not_gt hmid_130_137
              by_cases hmid_133_137 : p.val < 540
              · by_cases hmid_133_135 : p.val < 536
                · exact step_check_chunk_133 p hlo_133_137 hmid_133_135
                · have hlo_134_135 : 536 ≤ p.val := Nat.le_of_not_gt hmid_133_135
                  exact step_check_chunk_134 p hlo_134_135 hmid_133_137
              · have hlo_135_137 : 540 ≤ p.val := Nat.le_of_not_gt hmid_133_137
                by_cases hmid_135_137 : p.val < 544
                · exact step_check_chunk_135 p hlo_135_137 hmid_135_137
                · have hlo_136_137 : 544 ≤ p.val := Nat.le_of_not_gt hmid_135_137
                  exact step_check_chunk_136 p hlo_136_137 hmid_130_145
          · have hlo_137_145 : 548 ≤ p.val := Nat.le_of_not_gt hmid_130_145
            by_cases hmid_137_145 : p.val < 564
            · by_cases hmid_137_141 : p.val < 556
              · by_cases hmid_137_139 : p.val < 552
                · exact step_check_chunk_137 p hlo_137_145 hmid_137_139
                · have hlo_138_139 : 552 ≤ p.val := Nat.le_of_not_gt hmid_137_139
                  exact step_check_chunk_138 p hlo_138_139 hmid_137_141
              · have hlo_139_141 : 556 ≤ p.val := Nat.le_of_not_gt hmid_137_141
                by_cases hmid_139_141 : p.val < 560
                · exact step_check_chunk_139 p hlo_139_141 hmid_139_141
                · have hlo_140_141 : 560 ≤ p.val := Nat.le_of_not_gt hmid_139_141
                  exact step_check_chunk_140 p hlo_140_141 hmid_137_145
            · have hlo_141_145 : 564 ≤ p.val := Nat.le_of_not_gt hmid_137_145
              by_cases hmid_141_145 : p.val < 572
              · by_cases hmid_141_143 : p.val < 568
                · exact step_check_chunk_141 p hlo_141_145 hmid_141_143
                · have hlo_142_143 : 568 ≤ p.val := Nat.le_of_not_gt hmid_141_143
                  exact step_check_chunk_142 p hlo_142_143 hmid_141_145
              · have hlo_143_145 : 572 ≤ p.val := Nat.le_of_not_gt hmid_141_145
                by_cases hmid_143_145 : p.val < 576
                · exact step_check_chunk_143 p hlo_143_145 hmid_143_145
                · have hlo_144_145 : 576 ≤ p.val := Nat.le_of_not_gt hmid_143_145
                  exact step_check_chunk_144 p hlo_144_145 hmid_116_174
      · have hlo_145_174 : 580 ≤ p.val := Nat.le_of_not_gt hmid_116_174
        by_cases hmid_145_174 : p.val < 636
        · by_cases hmid_145_159 : p.val < 608
          · by_cases hmid_145_152 : p.val < 592
            · by_cases hmid_145_148 : p.val < 584
              · exact step_check_chunk_145 p hlo_145_174 hmid_145_148
              · have hlo_146_148 : 584 ≤ p.val := Nat.le_of_not_gt hmid_145_148
                by_cases hmid_146_148 : p.val < 588
                · exact step_check_chunk_146 p hlo_146_148 hmid_146_148
                · have hlo_147_148 : 588 ≤ p.val := Nat.le_of_not_gt hmid_146_148
                  exact step_check_chunk_147 p hlo_147_148 hmid_145_152
            · have hlo_148_152 : 592 ≤ p.val := Nat.le_of_not_gt hmid_145_152
              by_cases hmid_148_152 : p.val < 600
              · by_cases hmid_148_150 : p.val < 596
                · exact step_check_chunk_148 p hlo_148_152 hmid_148_150
                · have hlo_149_150 : 596 ≤ p.val := Nat.le_of_not_gt hmid_148_150
                  exact step_check_chunk_149 p hlo_149_150 hmid_148_152
              · have hlo_150_152 : 600 ≤ p.val := Nat.le_of_not_gt hmid_148_152
                by_cases hmid_150_152 : p.val < 604
                · exact step_check_chunk_150 p hlo_150_152 hmid_150_152
                · have hlo_151_152 : 604 ≤ p.val := Nat.le_of_not_gt hmid_150_152
                  exact step_check_chunk_151 p hlo_151_152 hmid_145_159
          · have hlo_152_159 : 608 ≤ p.val := Nat.le_of_not_gt hmid_145_159
            by_cases hmid_152_159 : p.val < 620
            · by_cases hmid_152_155 : p.val < 612
              · exact step_check_chunk_152 p hlo_152_159 hmid_152_155
              · have hlo_153_155 : 612 ≤ p.val := Nat.le_of_not_gt hmid_152_155
                by_cases hmid_153_155 : p.val < 616
                · exact step_check_chunk_153 p hlo_153_155 hmid_153_155
                · have hlo_154_155 : 616 ≤ p.val := Nat.le_of_not_gt hmid_153_155
                  exact step_check_chunk_154 p hlo_154_155 hmid_152_159
            · have hlo_155_159 : 620 ≤ p.val := Nat.le_of_not_gt hmid_152_159
              by_cases hmid_155_159 : p.val < 628
              · by_cases hmid_155_157 : p.val < 624
                · exact step_check_chunk_155 p hlo_155_159 hmid_155_157
                · have hlo_156_157 : 624 ≤ p.val := Nat.le_of_not_gt hmid_155_157
                  exact step_check_chunk_156 p hlo_156_157 hmid_155_159
              · have hlo_157_159 : 628 ≤ p.val := Nat.le_of_not_gt hmid_155_159
                by_cases hmid_157_159 : p.val < 632
                · exact step_check_chunk_157 p hlo_157_159 hmid_157_159
                · have hlo_158_159 : 632 ≤ p.val := Nat.le_of_not_gt hmid_157_159
                  exact step_check_chunk_158 p hlo_158_159 hmid_145_174
        · have hlo_159_174 : 636 ≤ p.val := Nat.le_of_not_gt hmid_145_174
          by_cases hmid_159_174 : p.val < 664
          · by_cases hmid_159_166 : p.val < 648
            · by_cases hmid_159_162 : p.val < 640
              · exact step_check_chunk_159 p hlo_159_174 hmid_159_162
              · have hlo_160_162 : 640 ≤ p.val := Nat.le_of_not_gt hmid_159_162
                by_cases hmid_160_162 : p.val < 644
                · exact step_check_chunk_160 p hlo_160_162 hmid_160_162
                · have hlo_161_162 : 644 ≤ p.val := Nat.le_of_not_gt hmid_160_162
                  exact step_check_chunk_161 p hlo_161_162 hmid_159_166
            · have hlo_162_166 : 648 ≤ p.val := Nat.le_of_not_gt hmid_159_166
              by_cases hmid_162_166 : p.val < 656
              · by_cases hmid_162_164 : p.val < 652
                · exact step_check_chunk_162 p hlo_162_166 hmid_162_164
                · have hlo_163_164 : 652 ≤ p.val := Nat.le_of_not_gt hmid_162_164
                  exact step_check_chunk_163 p hlo_163_164 hmid_162_166
              · have hlo_164_166 : 656 ≤ p.val := Nat.le_of_not_gt hmid_162_166
                by_cases hmid_164_166 : p.val < 660
                · exact step_check_chunk_164 p hlo_164_166 hmid_164_166
                · have hlo_165_166 : 660 ≤ p.val := Nat.le_of_not_gt hmid_164_166
                  exact step_check_chunk_165 p hlo_165_166 hmid_159_174
          · have hlo_166_174 : 664 ≤ p.val := Nat.le_of_not_gt hmid_159_174
            by_cases hmid_166_174 : p.val < 680
            · by_cases hmid_166_170 : p.val < 672
              · by_cases hmid_166_168 : p.val < 668
                · exact step_check_chunk_166 p hlo_166_174 hmid_166_168
                · have hlo_167_168 : 668 ≤ p.val := Nat.le_of_not_gt hmid_166_168
                  exact step_check_chunk_167 p hlo_167_168 hmid_166_170
              · have hlo_168_170 : 672 ≤ p.val := Nat.le_of_not_gt hmid_166_170
                by_cases hmid_168_170 : p.val < 676
                · exact step_check_chunk_168 p hlo_168_170 hmid_168_170
                · have hlo_169_170 : 676 ≤ p.val := Nat.le_of_not_gt hmid_168_170
                  exact step_check_chunk_169 p hlo_169_170 hmid_166_174
            · have hlo_170_174 : 680 ≤ p.val := Nat.le_of_not_gt hmid_166_174
              by_cases hmid_170_174 : p.val < 688
              · by_cases hmid_170_172 : p.val < 684
                · exact step_check_chunk_170 p hlo_170_174 hmid_170_172
                · have hlo_171_172 : 684 ≤ p.val := Nat.le_of_not_gt hmid_170_172
                  exact step_check_chunk_171 p hlo_171_172 hmid_170_174
              · have hlo_172_174 : 688 ≤ p.val := Nat.le_of_not_gt hmid_170_174
                by_cases hmid_172_174 : p.val < 692
                · exact step_check_chunk_172 p hlo_172_174 hmid_172_174
                · have hlo_173_174 : 692 ≤ p.val := Nat.le_of_not_gt hmid_172_174
                  exact step_check_chunk_173 p hlo_173_174 hmid_116_233
    · have hlo_174_233 : 696 ≤ p.val := Nat.le_of_not_gt hmid_116_233
      by_cases hmid_174_233 : p.val < 812
      · by_cases hmid_174_203 : p.val < 752
        · by_cases hmid_174_188 : p.val < 724
          · by_cases hmid_174_181 : p.val < 708
            · by_cases hmid_174_177 : p.val < 700
              · exact step_check_chunk_174 p hlo_174_233 hmid_174_177
              · have hlo_175_177 : 700 ≤ p.val := Nat.le_of_not_gt hmid_174_177
                by_cases hmid_175_177 : p.val < 704
                · exact step_check_chunk_175 p hlo_175_177 hmid_175_177
                · have hlo_176_177 : 704 ≤ p.val := Nat.le_of_not_gt hmid_175_177
                  exact step_check_chunk_176 p hlo_176_177 hmid_174_181
            · have hlo_177_181 : 708 ≤ p.val := Nat.le_of_not_gt hmid_174_181
              by_cases hmid_177_181 : p.val < 716
              · by_cases hmid_177_179 : p.val < 712
                · exact step_check_chunk_177 p hlo_177_181 hmid_177_179
                · have hlo_178_179 : 712 ≤ p.val := Nat.le_of_not_gt hmid_177_179
                  exact step_check_chunk_178 p hlo_178_179 hmid_177_181
              · have hlo_179_181 : 716 ≤ p.val := Nat.le_of_not_gt hmid_177_181
                by_cases hmid_179_181 : p.val < 720
                · exact step_check_chunk_179 p hlo_179_181 hmid_179_181
                · have hlo_180_181 : 720 ≤ p.val := Nat.le_of_not_gt hmid_179_181
                  exact step_check_chunk_180 p hlo_180_181 hmid_174_188
          · have hlo_181_188 : 724 ≤ p.val := Nat.le_of_not_gt hmid_174_188
            by_cases hmid_181_188 : p.val < 736
            · by_cases hmid_181_184 : p.val < 728
              · exact step_check_chunk_181 p hlo_181_188 hmid_181_184
              · have hlo_182_184 : 728 ≤ p.val := Nat.le_of_not_gt hmid_181_184
                by_cases hmid_182_184 : p.val < 732
                · exact step_check_chunk_182 p hlo_182_184 hmid_182_184
                · have hlo_183_184 : 732 ≤ p.val := Nat.le_of_not_gt hmid_182_184
                  exact step_check_chunk_183 p hlo_183_184 hmid_181_188
            · have hlo_184_188 : 736 ≤ p.val := Nat.le_of_not_gt hmid_181_188
              by_cases hmid_184_188 : p.val < 744
              · by_cases hmid_184_186 : p.val < 740
                · exact step_check_chunk_184 p hlo_184_188 hmid_184_186
                · have hlo_185_186 : 740 ≤ p.val := Nat.le_of_not_gt hmid_184_186
                  exact step_check_chunk_185 p hlo_185_186 hmid_184_188
              · have hlo_186_188 : 744 ≤ p.val := Nat.le_of_not_gt hmid_184_188
                by_cases hmid_186_188 : p.val < 748
                · exact step_check_chunk_186 p hlo_186_188 hmid_186_188
                · have hlo_187_188 : 748 ≤ p.val := Nat.le_of_not_gt hmid_186_188
                  exact step_check_chunk_187 p hlo_187_188 hmid_174_203
        · have hlo_188_203 : 752 ≤ p.val := Nat.le_of_not_gt hmid_174_203
          by_cases hmid_188_203 : p.val < 780
          · by_cases hmid_188_195 : p.val < 764
            · by_cases hmid_188_191 : p.val < 756
              · exact step_check_chunk_188 p hlo_188_203 hmid_188_191
              · have hlo_189_191 : 756 ≤ p.val := Nat.le_of_not_gt hmid_188_191
                by_cases hmid_189_191 : p.val < 760
                · exact step_check_chunk_189 p hlo_189_191 hmid_189_191
                · have hlo_190_191 : 760 ≤ p.val := Nat.le_of_not_gt hmid_189_191
                  exact step_check_chunk_190 p hlo_190_191 hmid_188_195
            · have hlo_191_195 : 764 ≤ p.val := Nat.le_of_not_gt hmid_188_195
              by_cases hmid_191_195 : p.val < 772
              · by_cases hmid_191_193 : p.val < 768
                · exact step_check_chunk_191 p hlo_191_195 hmid_191_193
                · have hlo_192_193 : 768 ≤ p.val := Nat.le_of_not_gt hmid_191_193
                  exact step_check_chunk_192 p hlo_192_193 hmid_191_195
              · have hlo_193_195 : 772 ≤ p.val := Nat.le_of_not_gt hmid_191_195
                by_cases hmid_193_195 : p.val < 776
                · exact step_check_chunk_193 p hlo_193_195 hmid_193_195
                · have hlo_194_195 : 776 ≤ p.val := Nat.le_of_not_gt hmid_193_195
                  exact step_check_chunk_194 p hlo_194_195 hmid_188_203
          · have hlo_195_203 : 780 ≤ p.val := Nat.le_of_not_gt hmid_188_203
            by_cases hmid_195_203 : p.val < 796
            · by_cases hmid_195_199 : p.val < 788
              · by_cases hmid_195_197 : p.val < 784
                · exact step_check_chunk_195 p hlo_195_203 hmid_195_197
                · have hlo_196_197 : 784 ≤ p.val := Nat.le_of_not_gt hmid_195_197
                  exact step_check_chunk_196 p hlo_196_197 hmid_195_199
              · have hlo_197_199 : 788 ≤ p.val := Nat.le_of_not_gt hmid_195_199
                by_cases hmid_197_199 : p.val < 792
                · exact step_check_chunk_197 p hlo_197_199 hmid_197_199
                · have hlo_198_199 : 792 ≤ p.val := Nat.le_of_not_gt hmid_197_199
                  exact step_check_chunk_198 p hlo_198_199 hmid_195_203
            · have hlo_199_203 : 796 ≤ p.val := Nat.le_of_not_gt hmid_195_203
              by_cases hmid_199_203 : p.val < 804
              · by_cases hmid_199_201 : p.val < 800
                · exact step_check_chunk_199 p hlo_199_203 hmid_199_201
                · have hlo_200_201 : 800 ≤ p.val := Nat.le_of_not_gt hmid_199_201
                  exact step_check_chunk_200 p hlo_200_201 hmid_199_203
              · have hlo_201_203 : 804 ≤ p.val := Nat.le_of_not_gt hmid_199_203
                by_cases hmid_201_203 : p.val < 808
                · exact step_check_chunk_201 p hlo_201_203 hmid_201_203
                · have hlo_202_203 : 808 ≤ p.val := Nat.le_of_not_gt hmid_201_203
                  exact step_check_chunk_202 p hlo_202_203 hmid_174_233
      · have hlo_203_233 : 812 ≤ p.val := Nat.le_of_not_gt hmid_174_233
        by_cases hmid_203_233 : p.val < 872
        · by_cases hmid_203_218 : p.val < 840
          · by_cases hmid_203_210 : p.val < 824
            · by_cases hmid_203_206 : p.val < 816
              · exact step_check_chunk_203 p hlo_203_233 hmid_203_206
              · have hlo_204_206 : 816 ≤ p.val := Nat.le_of_not_gt hmid_203_206
                by_cases hmid_204_206 : p.val < 820
                · exact step_check_chunk_204 p hlo_204_206 hmid_204_206
                · have hlo_205_206 : 820 ≤ p.val := Nat.le_of_not_gt hmid_204_206
                  exact step_check_chunk_205 p hlo_205_206 hmid_203_210
            · have hlo_206_210 : 824 ≤ p.val := Nat.le_of_not_gt hmid_203_210
              by_cases hmid_206_210 : p.val < 832
              · by_cases hmid_206_208 : p.val < 828
                · exact step_check_chunk_206 p hlo_206_210 hmid_206_208
                · have hlo_207_208 : 828 ≤ p.val := Nat.le_of_not_gt hmid_206_208
                  exact step_check_chunk_207 p hlo_207_208 hmid_206_210
              · have hlo_208_210 : 832 ≤ p.val := Nat.le_of_not_gt hmid_206_210
                by_cases hmid_208_210 : p.val < 836
                · exact step_check_chunk_208 p hlo_208_210 hmid_208_210
                · have hlo_209_210 : 836 ≤ p.val := Nat.le_of_not_gt hmid_208_210
                  exact step_check_chunk_209 p hlo_209_210 hmid_203_218
          · have hlo_210_218 : 840 ≤ p.val := Nat.le_of_not_gt hmid_203_218
            by_cases hmid_210_218 : p.val < 856
            · by_cases hmid_210_214 : p.val < 848
              · by_cases hmid_210_212 : p.val < 844
                · exact step_check_chunk_210 p hlo_210_218 hmid_210_212
                · have hlo_211_212 : 844 ≤ p.val := Nat.le_of_not_gt hmid_210_212
                  exact step_check_chunk_211 p hlo_211_212 hmid_210_214
              · have hlo_212_214 : 848 ≤ p.val := Nat.le_of_not_gt hmid_210_214
                by_cases hmid_212_214 : p.val < 852
                · exact step_check_chunk_212 p hlo_212_214 hmid_212_214
                · have hlo_213_214 : 852 ≤ p.val := Nat.le_of_not_gt hmid_212_214
                  exact step_check_chunk_213 p hlo_213_214 hmid_210_218
            · have hlo_214_218 : 856 ≤ p.val := Nat.le_of_not_gt hmid_210_218
              by_cases hmid_214_218 : p.val < 864
              · by_cases hmid_214_216 : p.val < 860
                · exact step_check_chunk_214 p hlo_214_218 hmid_214_216
                · have hlo_215_216 : 860 ≤ p.val := Nat.le_of_not_gt hmid_214_216
                  exact step_check_chunk_215 p hlo_215_216 hmid_214_218
              · have hlo_216_218 : 864 ≤ p.val := Nat.le_of_not_gt hmid_214_218
                by_cases hmid_216_218 : p.val < 868
                · exact step_check_chunk_216 p hlo_216_218 hmid_216_218
                · have hlo_217_218 : 868 ≤ p.val := Nat.le_of_not_gt hmid_216_218
                  exact step_check_chunk_217 p hlo_217_218 hmid_203_233
        · have hlo_218_233 : 872 ≤ p.val := Nat.le_of_not_gt hmid_203_233
          by_cases hmid_218_233 : p.val < 900
          · by_cases hmid_218_225 : p.val < 884
            · by_cases hmid_218_221 : p.val < 876
              · exact step_check_chunk_218 p hlo_218_233 hmid_218_221
              · have hlo_219_221 : 876 ≤ p.val := Nat.le_of_not_gt hmid_218_221
                by_cases hmid_219_221 : p.val < 880
                · exact step_check_chunk_219 p hlo_219_221 hmid_219_221
                · have hlo_220_221 : 880 ≤ p.val := Nat.le_of_not_gt hmid_219_221
                  exact step_check_chunk_220 p hlo_220_221 hmid_218_225
            · have hlo_221_225 : 884 ≤ p.val := Nat.le_of_not_gt hmid_218_225
              by_cases hmid_221_225 : p.val < 892
              · by_cases hmid_221_223 : p.val < 888
                · exact step_check_chunk_221 p hlo_221_225 hmid_221_223
                · have hlo_222_223 : 888 ≤ p.val := Nat.le_of_not_gt hmid_221_223
                  exact step_check_chunk_222 p hlo_222_223 hmid_221_225
              · have hlo_223_225 : 892 ≤ p.val := Nat.le_of_not_gt hmid_221_225
                by_cases hmid_223_225 : p.val < 896
                · exact step_check_chunk_223 p hlo_223_225 hmid_223_225
                · have hlo_224_225 : 896 ≤ p.val := Nat.le_of_not_gt hmid_223_225
                  exact step_check_chunk_224 p hlo_224_225 hmid_218_233
          · have hlo_225_233 : 900 ≤ p.val := Nat.le_of_not_gt hmid_218_233
            by_cases hmid_225_233 : p.val < 916
            · by_cases hmid_225_229 : p.val < 908
              · by_cases hmid_225_227 : p.val < 904
                · exact step_check_chunk_225 p hlo_225_233 hmid_225_227
                · have hlo_226_227 : 904 ≤ p.val := Nat.le_of_not_gt hmid_225_227
                  exact step_check_chunk_226 p hlo_226_227 hmid_225_229
              · have hlo_227_229 : 908 ≤ p.val := Nat.le_of_not_gt hmid_225_229
                by_cases hmid_227_229 : p.val < 912
                · exact step_check_chunk_227 p hlo_227_229 hmid_227_229
                · have hlo_228_229 : 912 ≤ p.val := Nat.le_of_not_gt hmid_227_229
                  exact step_check_chunk_228 p hlo_228_229 hmid_225_233
            · have hlo_229_233 : 916 ≤ p.val := Nat.le_of_not_gt hmid_225_233
              by_cases hmid_229_233 : p.val < 924
              · by_cases hmid_229_231 : p.val < 920
                · exact step_check_chunk_229 p hlo_229_233 hmid_229_231
                · have hlo_230_231 : 920 ≤ p.val := Nat.le_of_not_gt hmid_229_231
                  exact step_check_chunk_230 p hlo_230_231 hmid_229_233
              · have hlo_231_233 : 924 ≤ p.val := Nat.le_of_not_gt hmid_229_233
                by_cases hmid_231_233 : p.val < 928
                · exact step_check_chunk_231 p hlo_231_233 hmid_231_233
                · have hlo_232_233 : 928 ≤ p.val := Nat.le_of_not_gt hmid_231_233
                  exact step_check_chunk_232 p hlo_232_233 hhi_root

lemma step_checks : ∀ (p : Fin 929) (d e : Fin 2) (cp : Fin 9),
    9*d.val+cp.val=2*carry p+e.val → ∀ sp ∈ D.next (source p) d.val,
    R sp (target p d.val cp.val sp) cp.val ∧
    ∀ tp ∈ ends (target p d.val cp.val sp),
      parent p d.val cp.val sp tp ∈ ends p ∧
      tp ∈ D.next (parent p d.val cp.val sp tp) e.val ∧
      H p (parent p d.val cp.val sp tp)+W (parent p d.val cp.val sp tp) e.val tp-
        W (source p) d.val sp ≤ H (target p d.val cp.val sp) tp := by
  intro p d e cp har sp hsp
  have hd : d.val ∈ ([0,1] : List ℕ) := by
    have := d.isLt
    simp only [List.mem_cons, List.mem_singleton]
    omega
  have he : e.val ∈ ([0,1] : List ℕ) := by
    have := e.isLt
    simp only [List.mem_cons, List.mem_singleton]
    omega
  have ha : 9*d.val ≤ 2*carry p+e.val := by omega
  have hc : 2*carry p+e.val-9*d.val = cp.val := by omega
  have hb : 2*carry p+e.val-9*d.val < 9 := by rw [hc]; exact cp.isLt
  have hh := step_check_all p
  unfold stepCheck at hh
  have hh := List.all_eq_true.mp (List.all_eq_true.mp hh d.val hd) e.val he
  dsimp only at hh
  rw [if_pos ⟨ha,hb⟩, hc] at hh
  have hs : sp ∈ nextList (source p) d.val := by
    exact List.mem_toFinset.mp hsp
  have hz := Bool.and_eq_true_iff.mp (List.all_eq_true.mp hh sp hs)
  refine ⟨of_decide_eq_true hz.1, ?_⟩
  intro tp htp
  exact of_decide_eq_true (List.all_eq_true.mp hz.2 tp (List.mem_toFinset.mp htp))

def finishCheck (p : Fin 929) : Bool :=
  if carry p ∈ ([0,1,3,4] : List ℕ) ∧ F (source p) then
    decide (finish p ∈ ends p ∧ F (finish p) ∧ H p (finish p) ≤ 6000000)
  else true
lemma finish_check_chunk_0_small : ∀ p : Fin 16,
    finishCheck ⟨0+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma finish_check_chunk_0 (p : Fin 929) (hl : 0 ≤ p.val) (hh : p.val < 16) : finishCheck p = true := by
  let q : Fin 16 := ⟨p.val-0,by omega⟩
  have hp : (⟨0+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using finish_check_chunk_0_small q

lemma finish_check_chunk_1_small : ∀ p : Fin 16,
    finishCheck ⟨16+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma finish_check_chunk_1 (p : Fin 929) (hl : 16 ≤ p.val) (hh : p.val < 32) : finishCheck p = true := by
  let q : Fin 16 := ⟨p.val-16,by omega⟩
  have hp : (⟨16+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using finish_check_chunk_1_small q

lemma finish_check_chunk_2_small : ∀ p : Fin 16,
    finishCheck ⟨32+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma finish_check_chunk_2 (p : Fin 929) (hl : 32 ≤ p.val) (hh : p.val < 48) : finishCheck p = true := by
  let q : Fin 16 := ⟨p.val-32,by omega⟩
  have hp : (⟨32+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using finish_check_chunk_2_small q

lemma finish_check_chunk_3_small : ∀ p : Fin 16,
    finishCheck ⟨48+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma finish_check_chunk_3 (p : Fin 929) (hl : 48 ≤ p.val) (hh : p.val < 64) : finishCheck p = true := by
  let q : Fin 16 := ⟨p.val-48,by omega⟩
  have hp : (⟨48+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using finish_check_chunk_3_small q

lemma finish_check_chunk_4_small : ∀ p : Fin 16,
    finishCheck ⟨64+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma finish_check_chunk_4 (p : Fin 929) (hl : 64 ≤ p.val) (hh : p.val < 80) : finishCheck p = true := by
  let q : Fin 16 := ⟨p.val-64,by omega⟩
  have hp : (⟨64+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using finish_check_chunk_4_small q

lemma finish_check_chunk_5_small : ∀ p : Fin 16,
    finishCheck ⟨80+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma finish_check_chunk_5 (p : Fin 929) (hl : 80 ≤ p.val) (hh : p.val < 96) : finishCheck p = true := by
  let q : Fin 16 := ⟨p.val-80,by omega⟩
  have hp : (⟨80+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using finish_check_chunk_5_small q

lemma finish_check_chunk_6_small : ∀ p : Fin 16,
    finishCheck ⟨96+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma finish_check_chunk_6 (p : Fin 929) (hl : 96 ≤ p.val) (hh : p.val < 112) : finishCheck p = true := by
  let q : Fin 16 := ⟨p.val-96,by omega⟩
  have hp : (⟨96+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using finish_check_chunk_6_small q

lemma finish_check_chunk_7_small : ∀ p : Fin 16,
    finishCheck ⟨112+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma finish_check_chunk_7 (p : Fin 929) (hl : 112 ≤ p.val) (hh : p.val < 128) : finishCheck p = true := by
  let q : Fin 16 := ⟨p.val-112,by omega⟩
  have hp : (⟨112+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using finish_check_chunk_7_small q

lemma finish_check_chunk_8_small : ∀ p : Fin 16,
    finishCheck ⟨128+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma finish_check_chunk_8 (p : Fin 929) (hl : 128 ≤ p.val) (hh : p.val < 144) : finishCheck p = true := by
  let q : Fin 16 := ⟨p.val-128,by omega⟩
  have hp : (⟨128+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using finish_check_chunk_8_small q

lemma finish_check_chunk_9_small : ∀ p : Fin 16,
    finishCheck ⟨144+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma finish_check_chunk_9 (p : Fin 929) (hl : 144 ≤ p.val) (hh : p.val < 160) : finishCheck p = true := by
  let q : Fin 16 := ⟨p.val-144,by omega⟩
  have hp : (⟨144+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using finish_check_chunk_9_small q

lemma finish_check_chunk_10_small : ∀ p : Fin 16,
    finishCheck ⟨160+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma finish_check_chunk_10 (p : Fin 929) (hl : 160 ≤ p.val) (hh : p.val < 176) : finishCheck p = true := by
  let q : Fin 16 := ⟨p.val-160,by omega⟩
  have hp : (⟨160+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using finish_check_chunk_10_small q

lemma finish_check_chunk_11_small : ∀ p : Fin 16,
    finishCheck ⟨176+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma finish_check_chunk_11 (p : Fin 929) (hl : 176 ≤ p.val) (hh : p.val < 192) : finishCheck p = true := by
  let q : Fin 16 := ⟨p.val-176,by omega⟩
  have hp : (⟨176+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using finish_check_chunk_11_small q

lemma finish_check_chunk_12_small : ∀ p : Fin 16,
    finishCheck ⟨192+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma finish_check_chunk_12 (p : Fin 929) (hl : 192 ≤ p.val) (hh : p.val < 208) : finishCheck p = true := by
  let q : Fin 16 := ⟨p.val-192,by omega⟩
  have hp : (⟨192+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using finish_check_chunk_12_small q

lemma finish_check_chunk_13_small : ∀ p : Fin 16,
    finishCheck ⟨208+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma finish_check_chunk_13 (p : Fin 929) (hl : 208 ≤ p.val) (hh : p.val < 224) : finishCheck p = true := by
  let q : Fin 16 := ⟨p.val-208,by omega⟩
  have hp : (⟨208+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using finish_check_chunk_13_small q

lemma finish_check_chunk_14_small : ∀ p : Fin 16,
    finishCheck ⟨224+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma finish_check_chunk_14 (p : Fin 929) (hl : 224 ≤ p.val) (hh : p.val < 240) : finishCheck p = true := by
  let q : Fin 16 := ⟨p.val-224,by omega⟩
  have hp : (⟨224+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using finish_check_chunk_14_small q

lemma finish_check_chunk_15_small : ∀ p : Fin 16,
    finishCheck ⟨240+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma finish_check_chunk_15 (p : Fin 929) (hl : 240 ≤ p.val) (hh : p.val < 256) : finishCheck p = true := by
  let q : Fin 16 := ⟨p.val-240,by omega⟩
  have hp : (⟨240+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using finish_check_chunk_15_small q

lemma finish_check_chunk_16_small : ∀ p : Fin 16,
    finishCheck ⟨256+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma finish_check_chunk_16 (p : Fin 929) (hl : 256 ≤ p.val) (hh : p.val < 272) : finishCheck p = true := by
  let q : Fin 16 := ⟨p.val-256,by omega⟩
  have hp : (⟨256+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using finish_check_chunk_16_small q

lemma finish_check_chunk_17_small : ∀ p : Fin 16,
    finishCheck ⟨272+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma finish_check_chunk_17 (p : Fin 929) (hl : 272 ≤ p.val) (hh : p.val < 288) : finishCheck p = true := by
  let q : Fin 16 := ⟨p.val-272,by omega⟩
  have hp : (⟨272+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using finish_check_chunk_17_small q

lemma finish_check_chunk_18_small : ∀ p : Fin 16,
    finishCheck ⟨288+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma finish_check_chunk_18 (p : Fin 929) (hl : 288 ≤ p.val) (hh : p.val < 304) : finishCheck p = true := by
  let q : Fin 16 := ⟨p.val-288,by omega⟩
  have hp : (⟨288+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using finish_check_chunk_18_small q

lemma finish_check_chunk_19_small : ∀ p : Fin 16,
    finishCheck ⟨304+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma finish_check_chunk_19 (p : Fin 929) (hl : 304 ≤ p.val) (hh : p.val < 320) : finishCheck p = true := by
  let q : Fin 16 := ⟨p.val-304,by omega⟩
  have hp : (⟨304+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using finish_check_chunk_19_small q

lemma finish_check_chunk_20_small : ∀ p : Fin 16,
    finishCheck ⟨320+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma finish_check_chunk_20 (p : Fin 929) (hl : 320 ≤ p.val) (hh : p.val < 336) : finishCheck p = true := by
  let q : Fin 16 := ⟨p.val-320,by omega⟩
  have hp : (⟨320+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using finish_check_chunk_20_small q

lemma finish_check_chunk_21_small : ∀ p : Fin 16,
    finishCheck ⟨336+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma finish_check_chunk_21 (p : Fin 929) (hl : 336 ≤ p.val) (hh : p.val < 352) : finishCheck p = true := by
  let q : Fin 16 := ⟨p.val-336,by omega⟩
  have hp : (⟨336+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using finish_check_chunk_21_small q

lemma finish_check_chunk_22_small : ∀ p : Fin 16,
    finishCheck ⟨352+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma finish_check_chunk_22 (p : Fin 929) (hl : 352 ≤ p.val) (hh : p.val < 368) : finishCheck p = true := by
  let q : Fin 16 := ⟨p.val-352,by omega⟩
  have hp : (⟨352+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using finish_check_chunk_22_small q

lemma finish_check_chunk_23_small : ∀ p : Fin 16,
    finishCheck ⟨368+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma finish_check_chunk_23 (p : Fin 929) (hl : 368 ≤ p.val) (hh : p.val < 384) : finishCheck p = true := by
  let q : Fin 16 := ⟨p.val-368,by omega⟩
  have hp : (⟨368+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using finish_check_chunk_23_small q

lemma finish_check_chunk_24_small : ∀ p : Fin 16,
    finishCheck ⟨384+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma finish_check_chunk_24 (p : Fin 929) (hl : 384 ≤ p.val) (hh : p.val < 400) : finishCheck p = true := by
  let q : Fin 16 := ⟨p.val-384,by omega⟩
  have hp : (⟨384+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using finish_check_chunk_24_small q

lemma finish_check_chunk_25_small : ∀ p : Fin 16,
    finishCheck ⟨400+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma finish_check_chunk_25 (p : Fin 929) (hl : 400 ≤ p.val) (hh : p.val < 416) : finishCheck p = true := by
  let q : Fin 16 := ⟨p.val-400,by omega⟩
  have hp : (⟨400+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using finish_check_chunk_25_small q

lemma finish_check_chunk_26_small : ∀ p : Fin 16,
    finishCheck ⟨416+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma finish_check_chunk_26 (p : Fin 929) (hl : 416 ≤ p.val) (hh : p.val < 432) : finishCheck p = true := by
  let q : Fin 16 := ⟨p.val-416,by omega⟩
  have hp : (⟨416+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using finish_check_chunk_26_small q

lemma finish_check_chunk_27_small : ∀ p : Fin 16,
    finishCheck ⟨432+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma finish_check_chunk_27 (p : Fin 929) (hl : 432 ≤ p.val) (hh : p.val < 448) : finishCheck p = true := by
  let q : Fin 16 := ⟨p.val-432,by omega⟩
  have hp : (⟨432+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using finish_check_chunk_27_small q

lemma finish_check_chunk_28_small : ∀ p : Fin 16,
    finishCheck ⟨448+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma finish_check_chunk_28 (p : Fin 929) (hl : 448 ≤ p.val) (hh : p.val < 464) : finishCheck p = true := by
  let q : Fin 16 := ⟨p.val-448,by omega⟩
  have hp : (⟨448+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using finish_check_chunk_28_small q

lemma finish_check_chunk_29_small : ∀ p : Fin 16,
    finishCheck ⟨464+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma finish_check_chunk_29 (p : Fin 929) (hl : 464 ≤ p.val) (hh : p.val < 480) : finishCheck p = true := by
  let q : Fin 16 := ⟨p.val-464,by omega⟩
  have hp : (⟨464+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using finish_check_chunk_29_small q

lemma finish_check_chunk_30_small : ∀ p : Fin 16,
    finishCheck ⟨480+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma finish_check_chunk_30 (p : Fin 929) (hl : 480 ≤ p.val) (hh : p.val < 496) : finishCheck p = true := by
  let q : Fin 16 := ⟨p.val-480,by omega⟩
  have hp : (⟨480+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using finish_check_chunk_30_small q

lemma finish_check_chunk_31_small : ∀ p : Fin 16,
    finishCheck ⟨496+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma finish_check_chunk_31 (p : Fin 929) (hl : 496 ≤ p.val) (hh : p.val < 512) : finishCheck p = true := by
  let q : Fin 16 := ⟨p.val-496,by omega⟩
  have hp : (⟨496+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using finish_check_chunk_31_small q

lemma finish_check_chunk_32_small : ∀ p : Fin 16,
    finishCheck ⟨512+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma finish_check_chunk_32 (p : Fin 929) (hl : 512 ≤ p.val) (hh : p.val < 528) : finishCheck p = true := by
  let q : Fin 16 := ⟨p.val-512,by omega⟩
  have hp : (⟨512+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using finish_check_chunk_32_small q

lemma finish_check_chunk_33_small : ∀ p : Fin 16,
    finishCheck ⟨528+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma finish_check_chunk_33 (p : Fin 929) (hl : 528 ≤ p.val) (hh : p.val < 544) : finishCheck p = true := by
  let q : Fin 16 := ⟨p.val-528,by omega⟩
  have hp : (⟨528+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using finish_check_chunk_33_small q

lemma finish_check_chunk_34_small : ∀ p : Fin 16,
    finishCheck ⟨544+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma finish_check_chunk_34 (p : Fin 929) (hl : 544 ≤ p.val) (hh : p.val < 560) : finishCheck p = true := by
  let q : Fin 16 := ⟨p.val-544,by omega⟩
  have hp : (⟨544+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using finish_check_chunk_34_small q

lemma finish_check_chunk_35_small : ∀ p : Fin 16,
    finishCheck ⟨560+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma finish_check_chunk_35 (p : Fin 929) (hl : 560 ≤ p.val) (hh : p.val < 576) : finishCheck p = true := by
  let q : Fin 16 := ⟨p.val-560,by omega⟩
  have hp : (⟨560+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using finish_check_chunk_35_small q

lemma finish_check_chunk_36_small : ∀ p : Fin 16,
    finishCheck ⟨576+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma finish_check_chunk_36 (p : Fin 929) (hl : 576 ≤ p.val) (hh : p.val < 592) : finishCheck p = true := by
  let q : Fin 16 := ⟨p.val-576,by omega⟩
  have hp : (⟨576+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using finish_check_chunk_36_small q

lemma finish_check_chunk_37_small : ∀ p : Fin 16,
    finishCheck ⟨592+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma finish_check_chunk_37 (p : Fin 929) (hl : 592 ≤ p.val) (hh : p.val < 608) : finishCheck p = true := by
  let q : Fin 16 := ⟨p.val-592,by omega⟩
  have hp : (⟨592+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using finish_check_chunk_37_small q

lemma finish_check_chunk_38_small : ∀ p : Fin 16,
    finishCheck ⟨608+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma finish_check_chunk_38 (p : Fin 929) (hl : 608 ≤ p.val) (hh : p.val < 624) : finishCheck p = true := by
  let q : Fin 16 := ⟨p.val-608,by omega⟩
  have hp : (⟨608+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using finish_check_chunk_38_small q

lemma finish_check_chunk_39_small : ∀ p : Fin 16,
    finishCheck ⟨624+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma finish_check_chunk_39 (p : Fin 929) (hl : 624 ≤ p.val) (hh : p.val < 640) : finishCheck p = true := by
  let q : Fin 16 := ⟨p.val-624,by omega⟩
  have hp : (⟨624+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using finish_check_chunk_39_small q

lemma finish_check_chunk_40_small : ∀ p : Fin 16,
    finishCheck ⟨640+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma finish_check_chunk_40 (p : Fin 929) (hl : 640 ≤ p.val) (hh : p.val < 656) : finishCheck p = true := by
  let q : Fin 16 := ⟨p.val-640,by omega⟩
  have hp : (⟨640+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using finish_check_chunk_40_small q

lemma finish_check_chunk_41_small : ∀ p : Fin 16,
    finishCheck ⟨656+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma finish_check_chunk_41 (p : Fin 929) (hl : 656 ≤ p.val) (hh : p.val < 672) : finishCheck p = true := by
  let q : Fin 16 := ⟨p.val-656,by omega⟩
  have hp : (⟨656+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using finish_check_chunk_41_small q

lemma finish_check_chunk_42_small : ∀ p : Fin 16,
    finishCheck ⟨672+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma finish_check_chunk_42 (p : Fin 929) (hl : 672 ≤ p.val) (hh : p.val < 688) : finishCheck p = true := by
  let q : Fin 16 := ⟨p.val-672,by omega⟩
  have hp : (⟨672+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using finish_check_chunk_42_small q

lemma finish_check_chunk_43_small : ∀ p : Fin 16,
    finishCheck ⟨688+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma finish_check_chunk_43 (p : Fin 929) (hl : 688 ≤ p.val) (hh : p.val < 704) : finishCheck p = true := by
  let q : Fin 16 := ⟨p.val-688,by omega⟩
  have hp : (⟨688+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using finish_check_chunk_43_small q

lemma finish_check_chunk_44_small : ∀ p : Fin 16,
    finishCheck ⟨704+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma finish_check_chunk_44 (p : Fin 929) (hl : 704 ≤ p.val) (hh : p.val < 720) : finishCheck p = true := by
  let q : Fin 16 := ⟨p.val-704,by omega⟩
  have hp : (⟨704+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using finish_check_chunk_44_small q

lemma finish_check_chunk_45_small : ∀ p : Fin 16,
    finishCheck ⟨720+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma finish_check_chunk_45 (p : Fin 929) (hl : 720 ≤ p.val) (hh : p.val < 736) : finishCheck p = true := by
  let q : Fin 16 := ⟨p.val-720,by omega⟩
  have hp : (⟨720+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using finish_check_chunk_45_small q

lemma finish_check_chunk_46_small : ∀ p : Fin 16,
    finishCheck ⟨736+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma finish_check_chunk_46 (p : Fin 929) (hl : 736 ≤ p.val) (hh : p.val < 752) : finishCheck p = true := by
  let q : Fin 16 := ⟨p.val-736,by omega⟩
  have hp : (⟨736+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using finish_check_chunk_46_small q

lemma finish_check_chunk_47_small : ∀ p : Fin 16,
    finishCheck ⟨752+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma finish_check_chunk_47 (p : Fin 929) (hl : 752 ≤ p.val) (hh : p.val < 768) : finishCheck p = true := by
  let q : Fin 16 := ⟨p.val-752,by omega⟩
  have hp : (⟨752+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using finish_check_chunk_47_small q

lemma finish_check_chunk_48_small : ∀ p : Fin 16,
    finishCheck ⟨768+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma finish_check_chunk_48 (p : Fin 929) (hl : 768 ≤ p.val) (hh : p.val < 784) : finishCheck p = true := by
  let q : Fin 16 := ⟨p.val-768,by omega⟩
  have hp : (⟨768+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using finish_check_chunk_48_small q

lemma finish_check_chunk_49_small : ∀ p : Fin 16,
    finishCheck ⟨784+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma finish_check_chunk_49 (p : Fin 929) (hl : 784 ≤ p.val) (hh : p.val < 800) : finishCheck p = true := by
  let q : Fin 16 := ⟨p.val-784,by omega⟩
  have hp : (⟨784+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using finish_check_chunk_49_small q

lemma finish_check_chunk_50_small : ∀ p : Fin 16,
    finishCheck ⟨800+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma finish_check_chunk_50 (p : Fin 929) (hl : 800 ≤ p.val) (hh : p.val < 816) : finishCheck p = true := by
  let q : Fin 16 := ⟨p.val-800,by omega⟩
  have hp : (⟨800+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using finish_check_chunk_50_small q

lemma finish_check_chunk_51_small : ∀ p : Fin 16,
    finishCheck ⟨816+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma finish_check_chunk_51 (p : Fin 929) (hl : 816 ≤ p.val) (hh : p.val < 832) : finishCheck p = true := by
  let q : Fin 16 := ⟨p.val-816,by omega⟩
  have hp : (⟨816+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using finish_check_chunk_51_small q

lemma finish_check_chunk_52_small : ∀ p : Fin 16,
    finishCheck ⟨832+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma finish_check_chunk_52 (p : Fin 929) (hl : 832 ≤ p.val) (hh : p.val < 848) : finishCheck p = true := by
  let q : Fin 16 := ⟨p.val-832,by omega⟩
  have hp : (⟨832+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using finish_check_chunk_52_small q

lemma finish_check_chunk_53_small : ∀ p : Fin 16,
    finishCheck ⟨848+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma finish_check_chunk_53 (p : Fin 929) (hl : 848 ≤ p.val) (hh : p.val < 864) : finishCheck p = true := by
  let q : Fin 16 := ⟨p.val-848,by omega⟩
  have hp : (⟨848+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using finish_check_chunk_53_small q

lemma finish_check_chunk_54_small : ∀ p : Fin 16,
    finishCheck ⟨864+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma finish_check_chunk_54 (p : Fin 929) (hl : 864 ≤ p.val) (hh : p.val < 880) : finishCheck p = true := by
  let q : Fin 16 := ⟨p.val-864,by omega⟩
  have hp : (⟨864+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using finish_check_chunk_54_small q

lemma finish_check_chunk_55_small : ∀ p : Fin 16,
    finishCheck ⟨880+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma finish_check_chunk_55 (p : Fin 929) (hl : 880 ≤ p.val) (hh : p.val < 896) : finishCheck p = true := by
  let q : Fin 16 := ⟨p.val-880,by omega⟩
  have hp : (⟨880+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using finish_check_chunk_55_small q

lemma finish_check_chunk_56_small : ∀ p : Fin 16,
    finishCheck ⟨896+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma finish_check_chunk_56 (p : Fin 929) (hl : 896 ≤ p.val) (hh : p.val < 912) : finishCheck p = true := by
  let q : Fin 16 := ⟨p.val-896,by omega⟩
  have hp : (⟨896+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using finish_check_chunk_56_small q

lemma finish_check_chunk_57_small : ∀ p : Fin 16,
    finishCheck ⟨912+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma finish_check_chunk_57 (p : Fin 929) (hl : 912 ≤ p.val) (hh : p.val < 928) : finishCheck p = true := by
  let q : Fin 16 := ⟨p.val-912,by omega⟩
  have hp : (⟨912+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using finish_check_chunk_57_small q

lemma finish_check_chunk_58_small : ∀ p : Fin 1,
    finishCheck ⟨928+p.val,by have := p.isLt; omega⟩ = true := by decide +kernel
lemma finish_check_chunk_58 (p : Fin 929) (hl : 928 ≤ p.val) (hh : p.val < 929) : finishCheck p = true := by
  let q : Fin 1 := ⟨p.val-928,by omega⟩
  have hp : (⟨928+q.val,by have := q.isLt; omega⟩ : Fin 929) = p := by
    apply Fin.ext
    dsimp [q]
    omega
  simpa only [hp] using finish_check_chunk_58_small q

lemma finish_check_all (p : Fin 929) : finishCheck p = true := by
  have hlo_root : 0 ≤ p.val := Nat.zero_le _
  have hhi_root : p.val < 929 := p.isLt
  by_cases hmid_0_59 : p.val < 464
  · by_cases hmid_0_29 : p.val < 224
    · by_cases hmid_0_14 : p.val < 112
      · by_cases hmid_0_7 : p.val < 48
        · by_cases hmid_0_3 : p.val < 16
          · exact finish_check_chunk_0 p hlo_root hmid_0_3
          · have hlo_1_3 : 16 ≤ p.val := Nat.le_of_not_gt hmid_0_3
            by_cases hmid_1_3 : p.val < 32
            · exact finish_check_chunk_1 p hlo_1_3 hmid_1_3
            · have hlo_2_3 : 32 ≤ p.val := Nat.le_of_not_gt hmid_1_3
              exact finish_check_chunk_2 p hlo_2_3 hmid_0_7
        · have hlo_3_7 : 48 ≤ p.val := Nat.le_of_not_gt hmid_0_7
          by_cases hmid_3_7 : p.val < 80
          · by_cases hmid_3_5 : p.val < 64
            · exact finish_check_chunk_3 p hlo_3_7 hmid_3_5
            · have hlo_4_5 : 64 ≤ p.val := Nat.le_of_not_gt hmid_3_5
              exact finish_check_chunk_4 p hlo_4_5 hmid_3_7
          · have hlo_5_7 : 80 ≤ p.val := Nat.le_of_not_gt hmid_3_7
            by_cases hmid_5_7 : p.val < 96
            · exact finish_check_chunk_5 p hlo_5_7 hmid_5_7
            · have hlo_6_7 : 96 ≤ p.val := Nat.le_of_not_gt hmid_5_7
              exact finish_check_chunk_6 p hlo_6_7 hmid_0_14
      · have hlo_7_14 : 112 ≤ p.val := Nat.le_of_not_gt hmid_0_14
        by_cases hmid_7_14 : p.val < 160
        · by_cases hmid_7_10 : p.val < 128
          · exact finish_check_chunk_7 p hlo_7_14 hmid_7_10
          · have hlo_8_10 : 128 ≤ p.val := Nat.le_of_not_gt hmid_7_10
            by_cases hmid_8_10 : p.val < 144
            · exact finish_check_chunk_8 p hlo_8_10 hmid_8_10
            · have hlo_9_10 : 144 ≤ p.val := Nat.le_of_not_gt hmid_8_10
              exact finish_check_chunk_9 p hlo_9_10 hmid_7_14
        · have hlo_10_14 : 160 ≤ p.val := Nat.le_of_not_gt hmid_7_14
          by_cases hmid_10_14 : p.val < 192
          · by_cases hmid_10_12 : p.val < 176
            · exact finish_check_chunk_10 p hlo_10_14 hmid_10_12
            · have hlo_11_12 : 176 ≤ p.val := Nat.le_of_not_gt hmid_10_12
              exact finish_check_chunk_11 p hlo_11_12 hmid_10_14
          · have hlo_12_14 : 192 ≤ p.val := Nat.le_of_not_gt hmid_10_14
            by_cases hmid_12_14 : p.val < 208
            · exact finish_check_chunk_12 p hlo_12_14 hmid_12_14
            · have hlo_13_14 : 208 ≤ p.val := Nat.le_of_not_gt hmid_12_14
              exact finish_check_chunk_13 p hlo_13_14 hmid_0_29
    · have hlo_14_29 : 224 ≤ p.val := Nat.le_of_not_gt hmid_0_29
      by_cases hmid_14_29 : p.val < 336
      · by_cases hmid_14_21 : p.val < 272
        · by_cases hmid_14_17 : p.val < 240
          · exact finish_check_chunk_14 p hlo_14_29 hmid_14_17
          · have hlo_15_17 : 240 ≤ p.val := Nat.le_of_not_gt hmid_14_17
            by_cases hmid_15_17 : p.val < 256
            · exact finish_check_chunk_15 p hlo_15_17 hmid_15_17
            · have hlo_16_17 : 256 ≤ p.val := Nat.le_of_not_gt hmid_15_17
              exact finish_check_chunk_16 p hlo_16_17 hmid_14_21
        · have hlo_17_21 : 272 ≤ p.val := Nat.le_of_not_gt hmid_14_21
          by_cases hmid_17_21 : p.val < 304
          · by_cases hmid_17_19 : p.val < 288
            · exact finish_check_chunk_17 p hlo_17_21 hmid_17_19
            · have hlo_18_19 : 288 ≤ p.val := Nat.le_of_not_gt hmid_17_19
              exact finish_check_chunk_18 p hlo_18_19 hmid_17_21
          · have hlo_19_21 : 304 ≤ p.val := Nat.le_of_not_gt hmid_17_21
            by_cases hmid_19_21 : p.val < 320
            · exact finish_check_chunk_19 p hlo_19_21 hmid_19_21
            · have hlo_20_21 : 320 ≤ p.val := Nat.le_of_not_gt hmid_19_21
              exact finish_check_chunk_20 p hlo_20_21 hmid_14_29
      · have hlo_21_29 : 336 ≤ p.val := Nat.le_of_not_gt hmid_14_29
        by_cases hmid_21_29 : p.val < 400
        · by_cases hmid_21_25 : p.val < 368
          · by_cases hmid_21_23 : p.val < 352
            · exact finish_check_chunk_21 p hlo_21_29 hmid_21_23
            · have hlo_22_23 : 352 ≤ p.val := Nat.le_of_not_gt hmid_21_23
              exact finish_check_chunk_22 p hlo_22_23 hmid_21_25
          · have hlo_23_25 : 368 ≤ p.val := Nat.le_of_not_gt hmid_21_25
            by_cases hmid_23_25 : p.val < 384
            · exact finish_check_chunk_23 p hlo_23_25 hmid_23_25
            · have hlo_24_25 : 384 ≤ p.val := Nat.le_of_not_gt hmid_23_25
              exact finish_check_chunk_24 p hlo_24_25 hmid_21_29
        · have hlo_25_29 : 400 ≤ p.val := Nat.le_of_not_gt hmid_21_29
          by_cases hmid_25_29 : p.val < 432
          · by_cases hmid_25_27 : p.val < 416
            · exact finish_check_chunk_25 p hlo_25_29 hmid_25_27
            · have hlo_26_27 : 416 ≤ p.val := Nat.le_of_not_gt hmid_25_27
              exact finish_check_chunk_26 p hlo_26_27 hmid_25_29
          · have hlo_27_29 : 432 ≤ p.val := Nat.le_of_not_gt hmid_25_29
            by_cases hmid_27_29 : p.val < 448
            · exact finish_check_chunk_27 p hlo_27_29 hmid_27_29
            · have hlo_28_29 : 448 ≤ p.val := Nat.le_of_not_gt hmid_27_29
              exact finish_check_chunk_28 p hlo_28_29 hmid_0_59
  · have hlo_29_59 : 464 ≤ p.val := Nat.le_of_not_gt hmid_0_59
    by_cases hmid_29_59 : p.val < 704
    · by_cases hmid_29_44 : p.val < 576
      · by_cases hmid_29_36 : p.val < 512
        · by_cases hmid_29_32 : p.val < 480
          · exact finish_check_chunk_29 p hlo_29_59 hmid_29_32
          · have hlo_30_32 : 480 ≤ p.val := Nat.le_of_not_gt hmid_29_32
            by_cases hmid_30_32 : p.val < 496
            · exact finish_check_chunk_30 p hlo_30_32 hmid_30_32
            · have hlo_31_32 : 496 ≤ p.val := Nat.le_of_not_gt hmid_30_32
              exact finish_check_chunk_31 p hlo_31_32 hmid_29_36
        · have hlo_32_36 : 512 ≤ p.val := Nat.le_of_not_gt hmid_29_36
          by_cases hmid_32_36 : p.val < 544
          · by_cases hmid_32_34 : p.val < 528
            · exact finish_check_chunk_32 p hlo_32_36 hmid_32_34
            · have hlo_33_34 : 528 ≤ p.val := Nat.le_of_not_gt hmid_32_34
              exact finish_check_chunk_33 p hlo_33_34 hmid_32_36
          · have hlo_34_36 : 544 ≤ p.val := Nat.le_of_not_gt hmid_32_36
            by_cases hmid_34_36 : p.val < 560
            · exact finish_check_chunk_34 p hlo_34_36 hmid_34_36
            · have hlo_35_36 : 560 ≤ p.val := Nat.le_of_not_gt hmid_34_36
              exact finish_check_chunk_35 p hlo_35_36 hmid_29_44
      · have hlo_36_44 : 576 ≤ p.val := Nat.le_of_not_gt hmid_29_44
        by_cases hmid_36_44 : p.val < 640
        · by_cases hmid_36_40 : p.val < 608
          · by_cases hmid_36_38 : p.val < 592
            · exact finish_check_chunk_36 p hlo_36_44 hmid_36_38
            · have hlo_37_38 : 592 ≤ p.val := Nat.le_of_not_gt hmid_36_38
              exact finish_check_chunk_37 p hlo_37_38 hmid_36_40
          · have hlo_38_40 : 608 ≤ p.val := Nat.le_of_not_gt hmid_36_40
            by_cases hmid_38_40 : p.val < 624
            · exact finish_check_chunk_38 p hlo_38_40 hmid_38_40
            · have hlo_39_40 : 624 ≤ p.val := Nat.le_of_not_gt hmid_38_40
              exact finish_check_chunk_39 p hlo_39_40 hmid_36_44
        · have hlo_40_44 : 640 ≤ p.val := Nat.le_of_not_gt hmid_36_44
          by_cases hmid_40_44 : p.val < 672
          · by_cases hmid_40_42 : p.val < 656
            · exact finish_check_chunk_40 p hlo_40_44 hmid_40_42
            · have hlo_41_42 : 656 ≤ p.val := Nat.le_of_not_gt hmid_40_42
              exact finish_check_chunk_41 p hlo_41_42 hmid_40_44
          · have hlo_42_44 : 672 ≤ p.val := Nat.le_of_not_gt hmid_40_44
            by_cases hmid_42_44 : p.val < 688
            · exact finish_check_chunk_42 p hlo_42_44 hmid_42_44
            · have hlo_43_44 : 688 ≤ p.val := Nat.le_of_not_gt hmid_42_44
              exact finish_check_chunk_43 p hlo_43_44 hmid_29_59
    · have hlo_44_59 : 704 ≤ p.val := Nat.le_of_not_gt hmid_29_59
      by_cases hmid_44_59 : p.val < 816
      · by_cases hmid_44_51 : p.val < 752
        · by_cases hmid_44_47 : p.val < 720
          · exact finish_check_chunk_44 p hlo_44_59 hmid_44_47
          · have hlo_45_47 : 720 ≤ p.val := Nat.le_of_not_gt hmid_44_47
            by_cases hmid_45_47 : p.val < 736
            · exact finish_check_chunk_45 p hlo_45_47 hmid_45_47
            · have hlo_46_47 : 736 ≤ p.val := Nat.le_of_not_gt hmid_45_47
              exact finish_check_chunk_46 p hlo_46_47 hmid_44_51
        · have hlo_47_51 : 752 ≤ p.val := Nat.le_of_not_gt hmid_44_51
          by_cases hmid_47_51 : p.val < 784
          · by_cases hmid_47_49 : p.val < 768
            · exact finish_check_chunk_47 p hlo_47_51 hmid_47_49
            · have hlo_48_49 : 768 ≤ p.val := Nat.le_of_not_gt hmid_47_49
              exact finish_check_chunk_48 p hlo_48_49 hmid_47_51
          · have hlo_49_51 : 784 ≤ p.val := Nat.le_of_not_gt hmid_47_51
            by_cases hmid_49_51 : p.val < 800
            · exact finish_check_chunk_49 p hlo_49_51 hmid_49_51
            · have hlo_50_51 : 800 ≤ p.val := Nat.le_of_not_gt hmid_49_51
              exact finish_check_chunk_50 p hlo_50_51 hmid_44_59
      · have hlo_51_59 : 816 ≤ p.val := Nat.le_of_not_gt hmid_44_59
        by_cases hmid_51_59 : p.val < 880
        · by_cases hmid_51_55 : p.val < 848
          · by_cases hmid_51_53 : p.val < 832
            · exact finish_check_chunk_51 p hlo_51_59 hmid_51_53
            · have hlo_52_53 : 832 ≤ p.val := Nat.le_of_not_gt hmid_51_53
              exact finish_check_chunk_52 p hlo_52_53 hmid_51_55
          · have hlo_53_55 : 848 ≤ p.val := Nat.le_of_not_gt hmid_51_55
            by_cases hmid_53_55 : p.val < 864
            · exact finish_check_chunk_53 p hlo_53_55 hmid_53_55
            · have hlo_54_55 : 864 ≤ p.val := Nat.le_of_not_gt hmid_53_55
              exact finish_check_chunk_54 p hlo_54_55 hmid_51_59
        · have hlo_55_59 : 880 ≤ p.val := Nat.le_of_not_gt hmid_51_59
          by_cases hmid_55_59 : p.val < 912
          · by_cases hmid_55_57 : p.val < 896
            · exact finish_check_chunk_55 p hlo_55_59 hmid_55_57
            · have hlo_56_57 : 896 ≤ p.val := Nat.le_of_not_gt hmid_55_57
              exact finish_check_chunk_56 p hlo_56_57 hmid_55_59
          · have hlo_57_59 : 912 ≤ p.val := Nat.le_of_not_gt hmid_55_59
            by_cases hmid_57_59 : p.val < 928
            · exact finish_check_chunk_57 p hlo_57_59 hmid_57_59
            · have hlo_58_59 : 928 ≤ p.val := Nat.le_of_not_gt hmid_57_59
              exact finish_check_chunk_58 p hlo_58_59 hhi_root

lemma finish_checks : ∀ p : Fin 929, carry p ∈ ([0,1,3,4] : List ℕ) → F (source p) →
    finish p ∈ ends p ∧ F (finish p) ∧ H p (finish p) ≤ 6000000 := by
  intro p hc hf
  have hh := finish_check_all p
  unfold finishCheck at hh
  rw [if_pos ⟨hc,hf⟩] at hh
  exact of_decide_eq_true hh

def construction : Erdos406BinaryGroupedProfile.Construction 2 D F (Fin 929) where
  endpoints p t := t ∈ ends p
  R := R
  H _ p _ t := (H p t:ℝ)/3000000
  seed := by
    intro c hc
    interval_cases c
    · exact ⟨0,seed_relation_0,seed_runs_0⟩
    · exact ⟨1,seed_relation_1,seed_runs_1⟩
    · exact ⟨2,seed_relation_2,seed_runs_2⟩
    · exact ⟨3,seed_relation_3,seed_runs_3⟩
    · exact ⟨4,seed_relation_4,seed_runs_4⟩
    · exact ⟨5,seed_relation_5,seed_runs_5⟩
    · exact ⟨6,seed_relation_6,seed_runs_6⟩
    · exact ⟨7,seed_relation_7,seed_runs_7⟩
    · exact ⟨8,seed_relation_8,seed_runs_8⟩
  step := by
    intro s p c d e cp hc hd he hcp har hr sp hsp
    rcases hr with ⟨rfl,rfl⟩
    obtain ⟨hr',hs⟩ := step_checks p ⟨d,hd⟩ ⟨e,he⟩ ⟨cp,hcp⟩ har sp hsp
    refine ⟨target p d cp sp,hr',?_⟩
    intro tp ht
    obtain ⟨hp,he',hh⟩ := hs tp ht
    refine ⟨parent p d cp sp tp,hp,he',?_⟩
    have hR : (H p (parent p d cp sp tp):ℝ)+W (parent p d cp sp tp) e tp-
        W (source p) d sp ≤ H (target p d cp sp) tp := by exact_mod_cast hh
    change (H p (parent p d cp sp tp):ℝ)/3000000+(W (parent p d cp sp tp) e tp:ℝ)/3000000-
      (W (source p) d sp:ℝ)/3000000 ≤ (H (target p d cp sp) tp:ℝ)/3000000
    linarith
  finish := by
    intro s p c hc hr hf
    rcases hr with ⟨rfl,rfl⟩
    obtain ⟨ht,hf',hh⟩ := finish_checks p ((Erdos406GroupedCertificate.goodBlock_two_iff (carry p)).mp hc) hf
    refine ⟨finish p,ht,hf',?_⟩
    have hR : (H p (finish p):ℝ) ≤ 6000000 := by exact_mod_cast hh
    change (H p (finish p):ℝ)/3000000 ≤ 2
    linarith

def G (s : Fin 74) : Prop := s.val ∈ [1,2,5,13,20,44,72]
def Z (s : Fin 74) : Prop := s.val ∉ [72]
instance (s : Fin 74) : Decidable (G s) := by unfold G; infer_instance
instance (s : Fin 74) : Decidable (Z s) := by unfold Z; infer_instance
lemma power_checks :
    (∀ s, s ∈ D.next D.start 1 → G s) ∧
    (∀ s, G s → ∀ t ∈ D.next s 0, G t) ∧
    (∀ t, F t → Z t) ∧
    (∀ s, ∀ t ∈ D.next s 0, Z t → Z s) ∧
    (∀ s, G s → ∀ t ∈ D.next s 0, Z t → 1888797+J t-J s ≤ W s 0 t) ∧
    (∀ s ∈ D.next D.start 1, ∀ t, G t → F t → Z s → -3000000 ≤ W D.start 1 s+J t-J s) := by decide +kernel

def powerBound : PowerBound D F where
  a := 1888797/3000000
  B := 1
  G := G
  Z := Z
  J s := (J s:ℝ)/3000000
  start := power_checks.1
  forward := by intro s t hs ht; exact power_checks.2.1 s hs t ht
  accepting := power_checks.2.2.1
  backward := by intro s t ht he; exact power_checks.2.2.2.1 s t he ht
  lower_step := by
    intro s t hs hz he
    have hh : (1888797:ℝ)+J t-J s ≤ W s 0 t := by exact_mod_cast power_checks.2.2.2.2.1 s hs t he hz
    change (1888797/3000000:ℝ)+(J t:ℝ)/3000000-(J s:ℝ)/3000000 ≤ (W s 0 t:ℝ)/3000000
    linarith
  lower_end := by
    intro s t hs ht hf hz
    have hh : (-3000000:ℝ) ≤ W D.start 1 s+J t-J s := by exact_mod_cast power_checks.2.2.2.2.2 s hs t ht hf hz
    change -(1:ℝ) ≤ (W D.start 1 s:ℝ)/3000000+(J t:ℝ)/3000000-(J s:ℝ)/3000000
    linarith

lemma start_accepts : F D.start := by decide +kernel
lemma good_run_bound (n : ℕ) (hg : Nat.digits 3 n ⊆ [0,1]) :
    ∃ t v, Run D D.start (Nat.digits 2 n).reverse t v ∧ F t ∧
      v ≤ (2:ℝ)*(Nat.digits 9 n).length :=
  Erdos406BinaryGroupedProfile.Construction.exists_good_run construction (by decide) start_accepts n hg
lemma accepted_power_lower (k : ℕ) {t v}
    (hr : Run D D.start (Nat.digits 2 (2^k)).reverse t v) (hF : F t) :
    (1888797/3000000:ℝ)*k-1 ≤ v := by
  have hword : (Nat.digits 2 (2^k)).reverse = 1::List.replicate k 0 := by
    have hh := Nat.digits_base_pow_mul (b:=2) (k:=k) (m:=1) (by decide) (by decide)
    simpa using congrArg List.reverse hh
  exact powerBound.power_run_lower k (hword ▸ hr) hF

lemma not_supercritical : ¬ Real.log 2 < (1888797/3000000:ℝ)*Real.log 3 := by
  have hn : (3:ℕ)^17 ≤ 2^27 := by decide +kernel
  have hh : (3:ℝ)^17 ≤ (2:ℝ)^27 := by exact_mod_cast hn
  have hl := Real.log_le_log (by positivity : (0:ℝ)<3^17) hh
  rw [Real.log_pow,Real.log_pow] at hl
  have h3 := Real.log_pos (by norm_num : (1:ℝ)<3)
  norm_num only [Nat.cast_ofNat] at hl
  nlinarith

end
end Erdos406GroupedDeadTripleExported

#print axioms Erdos406GroupedDeadTripleExported.construction
#print axioms Erdos406GroupedDeadTripleExported.powerBound
#print axioms Erdos406GroupedDeadTripleExported.good_run_bound
#print axioms Erdos406GroupedDeadTripleExported.accepted_power_lower
#print axioms Erdos406GroupedDeadTripleExported.not_supercritical
