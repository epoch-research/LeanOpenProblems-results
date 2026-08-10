  interval_cases n
  · contradiction
  · exfalso
    have h_rep : A335624_rep 1 := by use 0, 0, 0, 1; decide
    exact (A335624_eq_zero_iff_not_rep 1).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 2 := by use 0, 0, 1, 1; decide
    exact (A335624_eq_zero_iff_not_rep 2).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 3 := by use 1, 1, 0, 1; decide
    exact (A335624_eq_zero_iff_not_rep 3).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 4 := by use 0, 0, 0, 2; decide
    exact (A335624_eq_zero_iff_not_rep 4).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 5 := by use 0, 0, 1, 2; decide
    exact (A335624_eq_zero_iff_not_rep 5).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 6 := by use 1, 0, 2, 1; decide
    exact (A335624_eq_zero_iff_not_rep 6).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 7 := by use 2, 1, 1, 1; decide
    exact (A335624_eq_zero_iff_not_rep 7).mp h h_rep
  · refine ⟨0, 1, by decide, by decide⟩
  · exfalso
    have h_rep : A335624_rep 9 := by use 0, 0, 0, 3; decide
    exact (A335624_eq_zero_iff_not_rep 9).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 10 := by use 0, 0, 1, 3; decide
    exact (A335624_eq_zero_iff_not_rep 10).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 11 := by use 1, 1, 0, 3; decide
    exact (A335624_eq_zero_iff_not_rep 11).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 12 := by use 1, 1, 3, 1; decide
    exact (A335624_eq_zero_iff_not_rep 12).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 13 := by use 0, 3, 0, 2; decide
    exact (A335624_eq_zero_iff_not_rep 13).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 14 := by use 1, 0, 2, 3; decide
    exact (A335624_eq_zero_iff_not_rep 14).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 15 := by use 1, 1, 3, 2; decide
    exact (A335624_eq_zero_iff_not_rep 15).mp h h_rep
  · exfalso; apply h16; decide
  · exfalso
    have h_rep : A335624_rep 17 := by use 0, 0, 1, 4; decide
    exact (A335624_eq_zero_iff_not_rep 17).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 18 := by use 0, 3, 0, 3; decide
    exact (A335624_eq_zero_iff_not_rep 18).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 19 := by use 3, 3, 1, 0; decide
    exact (A335624_eq_zero_iff_not_rep 19).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 20 := by use 0, 0, 4, 2; decide
    exact (A335624_eq_zero_iff_not_rep 20).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 21 := by use 0, 4, 1, 2; decide
    exact (A335624_eq_zero_iff_not_rep 21).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 22 := by use 2, 1, 1, 4; decide
    exact (A335624_eq_zero_iff_not_rep 22).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 23 := by use 3, 3, 1, 2; decide
    exact (A335624_eq_zero_iff_not_rep 23).mp h h_rep
  · refine ⟨0, 3, by decide, by decide⟩
  · exfalso
    have h_rep : A335624_rep 25 := by use 0, 0, 0, 5; decide
    exact (A335624_eq_zero_iff_not_rep 25).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 26 := by use 0, 0, 1, 5; decide
    exact (A335624_eq_zero_iff_not_rep 26).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 27 := by use 1, 1, 0, 5; decide
    exact (A335624_eq_zero_iff_not_rep 27).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 28 := by use 2, 2, 2, 4; decide
    exact (A335624_eq_zero_iff_not_rep 28).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 29 := by use 0, 3, 4, 2; decide
    exact (A335624_eq_zero_iff_not_rep 29).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 30 := by use 1, 0, 2, 5; decide
    exact (A335624_eq_zero_iff_not_rep 30).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 31 := by use 2, 1, 1, 5; decide
    exact (A335624_eq_zero_iff_not_rep 31).mp h h_rep
  · exfalso; apply h16; decide
  · exfalso
    have h_rep : A335624_rep 33 := by use 0, 4, 1, 4; decide
    exact (A335624_eq_zero_iff_not_rep 33).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 34 := by use 0, 3, 0, 5; decide
    exact (A335624_eq_zero_iff_not_rep 34).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 35 := by use 1, 4, 3, 3; decide
    exact (A335624_eq_zero_iff_not_rep 35).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 36 := by use 0, 0, 0, 6; decide
    exact (A335624_eq_zero_iff_not_rep 36).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 37 := by use 0, 0, 1, 6; decide
    exact (A335624_eq_zero_iff_not_rep 37).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 38 := by use 1, 0, 6, 1; decide
    exact (A335624_eq_zero_iff_not_rep 38).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 39 := by use 2, 1, 5, 3; decide
    exact (A335624_eq_zero_iff_not_rep 39).mp h h_rep
  · refine ⟨0, 5, by decide, by decide⟩
  · exfalso
    have h_rep : A335624_rep 41 := by use 0, 0, 4, 5; decide
    exact (A335624_eq_zero_iff_not_rep 41).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 42 := by use 0, 4, 1, 5; decide
    exact (A335624_eq_zero_iff_not_rep 42).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 43 := by use 4, 3, 3, 3; decide
    exact (A335624_eq_zero_iff_not_rep 43).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 44 := by use 3, 3, 1, 5; decide
    exact (A335624_eq_zero_iff_not_rep 44).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 45 := by use 0, 3, 0, 6; decide
    exact (A335624_eq_zero_iff_not_rep 45).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 46 := by use 1, 0, 6, 3; decide
    exact (A335624_eq_zero_iff_not_rep 46).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 47 := by use 1, 1, 3, 6; decide
    exact (A335624_eq_zero_iff_not_rep 47).mp h h_rep
  · exfalso; apply h16; decide
  · exfalso
    have h_rep : A335624_rep 49 := by use 0, 0, 0, 7; decide
    exact (A335624_eq_zero_iff_not_rep 49).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 50 := by use 0, 0, 1, 7; decide
    exact (A335624_eq_zero_iff_not_rep 50).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 51 := by use 0, 7, 1, 1; decide
    exact (A335624_eq_zero_iff_not_rep 51).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 52 := by use 0, 0, 4, 6; decide
    exact (A335624_eq_zero_iff_not_rep 52).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 53 := by use 0, 4, 1, 6; decide
    exact (A335624_eq_zero_iff_not_rep 53).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 54 := by use 0, 7, 1, 2; decide
    exact (A335624_eq_zero_iff_not_rep 54).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 55 := by use 1, 5, 5, 2; decide
    exact (A335624_eq_zero_iff_not_rep 55).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 56 := by use 0, 4, 6, 2; decide
    exact (A335624_eq_zero_iff_not_rep 56).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 57 := by use 2, 2, 7, 0; decide
    exact (A335624_eq_zero_iff_not_rep 57).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 58 := by use 0, 3, 0, 7; decide
    exact (A335624_eq_zero_iff_not_rep 58).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 59 := by use 0, 7, 1, 3; decide
    exact (A335624_eq_zero_iff_not_rep 59).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 60 := by use 1, 1, 3, 7; decide
    exact (A335624_eq_zero_iff_not_rep 60).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 61 := by use 0, 3, 4, 6; decide
    exact (A335624_eq_zero_iff_not_rep 61).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 62 := by use 1, 0, 6, 5; decide
    exact (A335624_eq_zero_iff_not_rep 62).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 63 := by use 3, 3, 6, 3; decide
    exact (A335624_eq_zero_iff_not_rep 63).mp h h_rep
  · exfalso; apply h16; decide
  · exfalso
    have h_rep : A335624_rep 65 := by use 0, 0, 1, 8; decide
    exact (A335624_eq_zero_iff_not_rep 65).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 66 := by use 0, 4, 1, 7; decide
    exact (A335624_eq_zero_iff_not_rep 66).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 67 := by use 1, 1, 8, 1; decide
    exact (A335624_eq_zero_iff_not_rep 67).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 68 := by use 0, 4, 6, 4; decide
    exact (A335624_eq_zero_iff_not_rep 68).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 69 := by use 1, 0, 2, 8; decide
    exact (A335624_eq_zero_iff_not_rep 69).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 70 := by use 1, 1, 8, 2; decide
    exact (A335624_eq_zero_iff_not_rep 70).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 71 := by use 3, 6, 1, 5; decide
    exact (A335624_eq_zero_iff_not_rep 71).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 72 := by use 2, 6, 4, 4; decide
    exact (A335624_eq_zero_iff_not_rep 72).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 73 := by use 0, 3, 0, 8; decide
    exact (A335624_eq_zero_iff_not_rep 73).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 74 := by use 0, 3, 4, 7; decide
    exact (A335624_eq_zero_iff_not_rep 74).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 75 := by use 0, 7, 1, 5; decide
    exact (A335624_eq_zero_iff_not_rep 75).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 76 := by use 1, 5, 5, 5; decide
    exact (A335624_eq_zero_iff_not_rep 76).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 77 := by use 0, 4, 6, 5; decide
    exact (A335624_eq_zero_iff_not_rep 77).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 78 := by use 3, 2, 4, 7; decide
    exact (A335624_eq_zero_iff_not_rep 78).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 79 := by use 2, 1, 5, 7; decide
    exact (A335624_eq_zero_iff_not_rep 79).mp h h_rep
  · exfalso; apply h16; decide
  · exfalso
    have h_rep : A335624_rep 81 := by use 0, 0, 0, 9; decide
    exact (A335624_eq_zero_iff_not_rep 81).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 82 := by use 0, 0, 1, 9; decide
    exact (A335624_eq_zero_iff_not_rep 82).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 83 := by use 1, 1, 0, 9; decide
    exact (A335624_eq_zero_iff_not_rep 83).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 84 := by use 4, 0, 8, 2; decide
    exact (A335624_eq_zero_iff_not_rep 84).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 85 := by use 0, 0, 9, 2; decide
    exact (A335624_eq_zero_iff_not_rep 85).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 86 := by use 0, 7, 1, 6; decide
    exact (A335624_eq_zero_iff_not_rep 86).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 87 := by use 1, 5, 5, 6; decide
    exact (A335624_eq_zero_iff_not_rep 87).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 88 := by use 0, 4, 6, 6; decide
    exact (A335624_eq_zero_iff_not_rep 88).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 89 := by use 0, 3, 4, 8; decide
    exact (A335624_eq_zero_iff_not_rep 89).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 90 := by use 0, 0, 9, 3; decide
    exact (A335624_eq_zero_iff_not_rep 90).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 91 := by use 1, 1, 8, 5; decide
    exact (A335624_eq_zero_iff_not_rep 91).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 92 := by use 1, 1, 3, 9; decide
    exact (A335624_eq_zero_iff_not_rep 92).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 93 := by use 2, 2, 2, 9; decide
    exact (A335624_eq_zero_iff_not_rep 93).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 94 := by use 2, 1, 5, 8; decide
    exact (A335624_eq_zero_iff_not_rep 94).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 95 := by use 1, 9, 2, 3; decide
    exact (A335624_eq_zero_iff_not_rep 95).mp h h_rep
  · exfalso; apply h16; decide
  · exfalso
    have h_rep : A335624_rep 97 := by use 0, 0, 4, 9; decide
    exact (A335624_eq_zero_iff_not_rep 97).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 98 := by use 0, 4, 1, 9; decide
    exact (A335624_eq_zero_iff_not_rep 98).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 99 := by use 0, 7, 1, 7; decide
    exact (A335624_eq_zero_iff_not_rep 99).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 100 := by use 0, 0, 0, 10; decide
    exact (A335624_eq_zero_iff_not_rep 100).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 101 := by use 0, 0, 1, 10; decide
    exact (A335624_eq_zero_iff_not_rep 101).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 102 := by use 0, 7, 7, 2; decide
    exact (A335624_eq_zero_iff_not_rep 102).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 103 := by use 3, 3, 6, 7; decide
    exact (A335624_eq_zero_iff_not_rep 103).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 104 := by use 8, 0, 2, 6; decide
    exact (A335624_eq_zero_iff_not_rep 104).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 105 := by use 1, 0, 2, 10; decide
    exact (A335624_eq_zero_iff_not_rep 105).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 106 := by use 0, 0, 9, 5; decide
    exact (A335624_eq_zero_iff_not_rep 106).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 107 := by use 0, 7, 7, 3; decide
    exact (A335624_eq_zero_iff_not_rep 107).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 108 := by use 5, 9, 1, 1; decide
    exact (A335624_eq_zero_iff_not_rep 108).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 109 := by use 0, 3, 0, 10; decide
    exact (A335624_eq_zero_iff_not_rep 109).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 110 := by use 0, 3, 10, 1; decide
    exact (A335624_eq_zero_iff_not_rep 110).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 111 := by use 1, 1, 3, 10; decide
    exact (A335624_eq_zero_iff_not_rep 111).mp h h_rep
  · exfalso; apply h16; decide
  · exfalso
    have h_rep : A335624_rep 113 := by use 0, 3, 10, 2; decide
    exact (A335624_eq_zero_iff_not_rep 113).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 114 := by use 0, 7, 1, 8; decide
    exact (A335624_eq_zero_iff_not_rep 114).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 115 := by use 1, 1, 8, 7; decide
    exact (A335624_eq_zero_iff_not_rep 115).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 116 := by use 0, 0, 4, 10; decide
    exact (A335624_eq_zero_iff_not_rep 116).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 117 := by use 0, 0, 9, 6; decide
    exact (A335624_eq_zero_iff_not_rep 117).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 118 := by use 0, 3, 10, 3; decide
    exact (A335624_eq_zero_iff_not_rep 118).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 119 := by use 2, 9, 5, 3; decide
    exact (A335624_eq_zero_iff_not_rep 119).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 120 := by use 2, 6, 4, 8; decide
    exact (A335624_eq_zero_iff_not_rep 120).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 121 := by use 0, 0, 0, 11; decide
    exact (A335624_eq_zero_iff_not_rep 121).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 122 := by use 0, 0, 1, 11; decide
    exact (A335624_eq_zero_iff_not_rep 122).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 123 := by use 0, 7, 7, 5; decide
    exact (A335624_eq_zero_iff_not_rep 123).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 124 := by use 5, 1, 7, 7; decide
    exact (A335624_eq_zero_iff_not_rep 124).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 125 := by use 0, 3, 4, 10; decide
    exact (A335624_eq_zero_iff_not_rep 125).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 126 := by use 1, 0, 2, 11; decide
    exact (A335624_eq_zero_iff_not_rep 126).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 127 := by use 2, 1, 1, 11; decide
    exact (A335624_eq_zero_iff_not_rep 127).mp h h_rep
  · exfalso; apply h16; decide
  · exfalso
    have h_rep : A335624_rep 129 := by use 1, 8, 0, 8; decide
    exact (A335624_eq_zero_iff_not_rep 129).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 130 := by use 0, 0, 9, 7; decide
    exact (A335624_eq_zero_iff_not_rep 130).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 131 := by use 0, 7, 1, 9; decide
    exact (A335624_eq_zero_iff_not_rep 131).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 132 := by use 1, 1, 3, 11; decide
    exact (A335624_eq_zero_iff_not_rep 132).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 133 := by use 0, 4, 6, 9; decide
    exact (A335624_eq_zero_iff_not_rep 133).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 134 := by use 0, 3, 10, 5; decide
    exact (A335624_eq_zero_iff_not_rep 134).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 135 := by use 1, 9, 2, 7; decide
    exact (A335624_eq_zero_iff_not_rep 135).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 136 := by use 6, 10, 0, 0; decide
    exact (A335624_eq_zero_iff_not_rep 136).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 137 := by use 0, 0, 4, 11; decide
    exact (A335624_eq_zero_iff_not_rep 137).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 138 := by use 0, 4, 1, 11; decide
    exact (A335624_eq_zero_iff_not_rep 138).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 139 := by use 3, 11, 0, 3; decide
    exact (A335624_eq_zero_iff_not_rep 139).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 140 := by use 3, 3, 1, 11; decide
    exact (A335624_eq_zero_iff_not_rep 140).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 141 := by use 0, 11, 4, 2; decide
    exact (A335624_eq_zero_iff_not_rep 141).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 142 := by use 2, 1, 11, 4; decide
    exact (A335624_eq_zero_iff_not_rep 142).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 143 := by use 3, 6, 7, 7; decide
    exact (A335624_eq_zero_iff_not_rep 143).mp h h_rep
  · exfalso; apply h16; decide
  · exfalso
    have h_rep : A335624_rep 145 := by use 0, 0, 1, 12; decide
    exact (A335624_eq_zero_iff_not_rep 145).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 146 := by use 0, 3, 4, 11; decide
    exact (A335624_eq_zero_iff_not_rep 146).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 147 := by use 0, 7, 7, 7; decide
    exact (A335624_eq_zero_iff_not_rep 147).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 148 := by use 0, 12, 0, 2; decide
    exact (A335624_eq_zero_iff_not_rep 148).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 149 := by use 1, 0, 2, 12; decide
    exact (A335624_eq_zero_iff_not_rep 149).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 150 := by use 0, 7, 1, 10; decide
    exact (A335624_eq_zero_iff_not_rep 150).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 151 := by use 1, 5, 5, 10; decide
    exact (A335624_eq_zero_iff_not_rep 151).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 152 := by use 0, 4, 6, 10; decide
    exact (A335624_eq_zero_iff_not_rep 152).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 153 := by use 0, 3, 0, 12; decide
    exact (A335624_eq_zero_iff_not_rep 153).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 154 := by use 0, 8, 3, 9; decide
    exact (A335624_eq_zero_iff_not_rep 154).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 155 := by use 1, 1, 3, 12; decide
    exact (A335624_eq_zero_iff_not_rep 155).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 156 := by use 2, 2, 2, 12; decide
    exact (A335624_eq_zero_iff_not_rep 156).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 157 := by use 2, 2, 7, 10; decide
    exact (A335624_eq_zero_iff_not_rep 157).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 158 := by use 0, 3, 10, 7; decide
    exact (A335624_eq_zero_iff_not_rep 158).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 159 := by use 2, 9, 5, 7; decide
    exact (A335624_eq_zero_iff_not_rep 159).mp h h_rep
  · exfalso; apply h16; decide
  · exfalso
    have h_rep : A335624_rep 161 := by use 0, 4, 1, 12; decide
    exact (A335624_eq_zero_iff_not_rep 161).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 162 := by use 0, 0, 9, 9; decide
    exact (A335624_eq_zero_iff_not_rep 162).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 163 := by use 1, 9, 9, 0; decide
    exact (A335624_eq_zero_iff_not_rep 163).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 164 := by use 0, 8, 10, 0; decide
    exact (A335624_eq_zero_iff_not_rep 164).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 165 := by use 0, 8, 10, 1; decide
    exact (A335624_eq_zero_iff_not_rep 165).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 166 := by use 1, 1, 8, 10; decide
    exact (A335624_eq_zero_iff_not_rep 166).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 167 := by use 1, 9, 2, 9; decide
    exact (A335624_eq_zero_iff_not_rep 167).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 168 := by use 0, 8, 10, 2; decide
    exact (A335624_eq_zero_iff_not_rep 168).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 169 := by use 0, 0, 0, 13; decide
    exact (A335624_eq_zero_iff_not_rep 169).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 170 := by use 0, 0, 1, 13; decide
    exact (A335624_eq_zero_iff_not_rep 170).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 171 := by use 0, 7, 1, 11; decide
    exact (A335624_eq_zero_iff_not_rep 171).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 172 := by use 1, 5, 5, 11; decide
    exact (A335624_eq_zero_iff_not_rep 172).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 173 := by use 0, 3, 10, 8; decide
    exact (A335624_eq_zero_iff_not_rep 173).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 174 := by use 1, 0, 2, 13; decide
    exact (A335624_eq_zero_iff_not_rep 174).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 175 := by use 2, 1, 1, 13; decide
    exact (A335624_eq_zero_iff_not_rep 175).mp h h_rep
  · exfalso; apply h16; decide
  · exfalso
    have h_rep : A335624_rep 177 := by use 2, 5, 2, 12; decide
    exact (A335624_eq_zero_iff_not_rep 177).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 178 := by use 0, 3, 0, 13; decide
    exact (A335624_eq_zero_iff_not_rep 178).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 179 := by use 0, 7, 7, 9; decide
    exact (A335624_eq_zero_iff_not_rep 179).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 180 := by use 0, 8, 10, 4; decide
    exact (A335624_eq_zero_iff_not_rep 180).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 181 := by use 0, 0, 9, 10; decide
    exact (A335624_eq_zero_iff_not_rep 181).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 182 := by use 1, 8, 6, 9; decide
    exact (A335624_eq_zero_iff_not_rep 182).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 183 := by use 3, 7, 10, 5; decide
    exact (A335624_eq_zero_iff_not_rep 183).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 184 := by use 2, 10, 8, 4; decide
    exact (A335624_eq_zero_iff_not_rep 184).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 185 := by use 0, 0, 4, 13; decide
    exact (A335624_eq_zero_iff_not_rep 185).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 186 := by use 0, 4, 1, 13; decide
    exact (A335624_eq_zero_iff_not_rep 186).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 187 := by use 1, 1, 8, 11; decide
    exact (A335624_eq_zero_iff_not_rep 187).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 188 := by use 1, 9, 9, 5; decide
    exact (A335624_eq_zero_iff_not_rep 188).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 189 := by use 0, 4, 13, 2; decide
    exact (A335624_eq_zero_iff_not_rep 189).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 190 := by use 0, 3, 10, 9; decide
    exact (A335624_eq_zero_iff_not_rep 190).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 191 := by use 2, 9, 5, 9; decide
    exact (A335624_eq_zero_iff_not_rep 191).mp h h_rep
  · exfalso; apply h16; decide
  · exfalso
    have h_rep : A335624_rep 193 := by use 0, 12, 0, 7; decide
    exact (A335624_eq_zero_iff_not_rep 193).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 194 := by use 0, 3, 4, 13; decide
    exact (A335624_eq_zero_iff_not_rep 194).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 195 := by use 1, 4, 3, 13; decide
    exact (A335624_eq_zero_iff_not_rep 195).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 196 := by use 0, 0, 0, 14; decide
    exact (A335624_eq_zero_iff_not_rep 196).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 197 := by use 0, 0, 1, 14; decide
    exact (A335624_eq_zero_iff_not_rep 197).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 198 := by use 0, 7, 7, 10; decide
    exact (A335624_eq_zero_iff_not_rep 198).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 199 := by use 1, 9, 9, 6; decide
    exact (A335624_eq_zero_iff_not_rep 199).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 200 := by use 0, 8, 10, 6; decide
    exact (A335624_eq_zero_iff_not_rep 200).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 201 := by use 0, 4, 13, 4; decide
    exact (A335624_eq_zero_iff_not_rep 201).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 202 := by use 0, 0, 9, 11; decide
    exact (A335624_eq_zero_iff_not_rep 202).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 203 := by use 1, 12, 3, 7; decide
    exact (A335624_eq_zero_iff_not_rep 203).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 204 := by use 2, 2, 14, 0; decide
    exact (A335624_eq_zero_iff_not_rep 204).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 205 := by use 0, 3, 0, 14; decide
    exact (A335624_eq_zero_iff_not_rep 205).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 206 := by use 1, 0, 6, 13; decide
    exact (A335624_eq_zero_iff_not_rep 206).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 207 := by use 1, 1, 3, 14; decide
    exact (A335624_eq_zero_iff_not_rep 207).mp h h_rep
  · exfalso; apply h16; decide
  · exfalso
    have h_rep : A335624_rep 209 := by use 0, 3, 10, 10; decide
    exact (A335624_eq_zero_iff_not_rep 209).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 210 := by use 0, 4, 13, 5; decide
    exact (A335624_eq_zero_iff_not_rep 210).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 211 := by use 3, 7, 3, 12; decide
    exact (A335624_eq_zero_iff_not_rep 211).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 212 := by use 0, 0, 4, 14; decide
    exact (A335624_eq_zero_iff_not_rep 212).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 213 := by use 0, 4, 1, 14; decide
    exact (A335624_eq_zero_iff_not_rep 213).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 214 := by use 2, 5, 8, 11; decide
    exact (A335624_eq_zero_iff_not_rep 214).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 215 := by use 1, 13, 6, 3; decide
    exact (A335624_eq_zero_iff_not_rep 215).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 216 := by use 12, 0, 6, 6; decide
    exact (A335624_eq_zero_iff_not_rep 216).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 217 := by use 0, 8, 3, 12; decide
    exact (A335624_eq_zero_iff_not_rep 217).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 218 := by use 0, 11, 4, 9; decide
    exact (A335624_eq_zero_iff_not_rep 218).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 219 := by use 0, 7, 1, 13; decide
    exact (A335624_eq_zero_iff_not_rep 219).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 220 := by use 1, 5, 5, 13; decide
    exact (A335624_eq_zero_iff_not_rep 220).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 221 := by use 0, 3, 4, 14; decide
    exact (A335624_eq_zero_iff_not_rep 221).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 222 := by use 1, 4, 3, 14; decide
    exact (A335624_eq_zero_iff_not_rep 222).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 223 := by use 3, 3, 6, 13; decide
    exact (A335624_eq_zero_iff_not_rep 223).mp h h_rep
  · exfalso; apply h16; decide
  · exfalso
    have h_rep : A335624_rep 225 := by use 0, 0, 0, 15; decide
    exact (A335624_eq_zero_iff_not_rep 225).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 226 := by use 0, 0, 1, 15; decide
    exact (A335624_eq_zero_iff_not_rep 226).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 227 := by use 0, 15, 1, 1; decide
    exact (A335624_eq_zero_iff_not_rep 227).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 228 := by use 0, 8, 10, 8; decide
    exact (A335624_eq_zero_iff_not_rep 228).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 229 := by use 0, 12, 7, 6; decide
    exact (A335624_eq_zero_iff_not_rep 229).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 230 := by use 0, 3, 10, 11; decide
    exact (A335624_eq_zero_iff_not_rep 230).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 231 := by use 1, 1, 15, 2; decide
    exact (A335624_eq_zero_iff_not_rep 231).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 232 := by use 2, 10, 8, 8; decide
    exact (A335624_eq_zero_iff_not_rep 232).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 233 := by use 1, 0, 6, 14; decide
    exact (A335624_eq_zero_iff_not_rep 233).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 234 := by use 0, 3, 0, 15; decide
    exact (A335624_eq_zero_iff_not_rep 234).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 235 := by use 0, 15, 1, 3; decide
    exact (A335624_eq_zero_iff_not_rep 235).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 236 := by use 1, 1, 3, 15; decide
    exact (A335624_eq_zero_iff_not_rep 236).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 237 := by use 0, 11, 4, 10; decide
    exact (A335624_eq_zero_iff_not_rep 237).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 238 := by use 3, 2, 0, 15; decide
    exact (A335624_eq_zero_iff_not_rep 238).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 239 := by use 3, 7, 10, 9; decide
    exact (A335624_eq_zero_iff_not_rep 239).mp h h_rep
  · exfalso; apply h16; decide
  · exfalso
    have h_rep : A335624_rep 241 := by use 0, 0, 4, 15; decide
    exact (A335624_eq_zero_iff_not_rep 241).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 242 := by use 0, 4, 1, 15; decide
    exact (A335624_eq_zero_iff_not_rep 242).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 243 := by use 1, 1, 15, 4; decide
    exact (A335624_eq_zero_iff_not_rep 243).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 244 := by use 0, 12, 0, 10; decide
    exact (A335624_eq_zero_iff_not_rep 244).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 245 := by use 0, 8, 10, 9; decide
    exact (A335624_eq_zero_iff_not_rep 245).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 246 := by use 0, 7, 1, 14; decide
    exact (A335624_eq_zero_iff_not_rep 246).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 247 := by use 1, 5, 5, 14; decide
    exact (A335624_eq_zero_iff_not_rep 247).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 248 := by use 0, 4, 6, 14; decide
    exact (A335624_eq_zero_iff_not_rep 248).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 249 := by use 0, 4, 13, 8; decide
    exact (A335624_eq_zero_iff_not_rep 249).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 250 := by use 0, 0, 9, 13; decide
    exact (A335624_eq_zero_iff_not_rep 250).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 251 := by use 0, 15, 1, 5; decide
    exact (A335624_eq_zero_iff_not_rep 251).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 252 := by use 1, 1, 15, 5; decide
    exact (A335624_eq_zero_iff_not_rep 252).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 253 := by use 0, 3, 10, 12; decide
    exact (A335624_eq_zero_iff_not_rep 253).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 254 := by use 1, 12, 3, 10; decide
    exact (A335624_eq_zero_iff_not_rep 254).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 255 := by use 1, 9, 2, 13; decide
    exact (A335624_eq_zero_iff_not_rep 255).mp h h_rep
  · exfalso; apply h16; decide
  · exfalso
    have h_rep : A335624_rep 257 := by use 0, 0, 1, 16; decide
    exact (A335624_eq_zero_iff_not_rep 257).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 258 := by use 0, 11, 4, 11; decide
    exact (A335624_eq_zero_iff_not_rep 258).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 259 := by use 3, 15, 4, 3; decide
    exact (A335624_eq_zero_iff_not_rep 259).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 260 := by use 0, 0, 16, 2; decide
    exact (A335624_eq_zero_iff_not_rep 260).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 261 := by use 1, 0, 2, 16; decide
    exact (A335624_eq_zero_iff_not_rep 261).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 262 := by use 0, 15, 1, 6; decide
    exact (A335624_eq_zero_iff_not_rep 262).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 263 := by use 1, 1, 15, 6; decide
    exact (A335624_eq_zero_iff_not_rep 263).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 264 := by use 0, 8, 10, 10; decide
    exact (A335624_eq_zero_iff_not_rep 264).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 265 := by use 0, 0, 16, 3; decide
    exact (A335624_eq_zero_iff_not_rep 265).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 266 := by use 0, 4, 13, 9; decide
    exact (A335624_eq_zero_iff_not_rep 266).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 267 := by use 0, 7, 7, 13; decide
    exact (A335624_eq_zero_iff_not_rep 267).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 268 := by use 2, 2, 2, 16; decide
    exact (A335624_eq_zero_iff_not_rep 268).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 269 := by use 0, 8, 3, 14; decide
    exact (A335624_eq_zero_iff_not_rep 269).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 270 := by use 1, 5, 12, 10; decide
    exact (A335624_eq_zero_iff_not_rep 270).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 271 := by use 3, 6, 1, 15; decide
    exact (A335624_eq_zero_iff_not_rep 271).mp h h_rep
  · exfalso; apply h16; decide
  · exfalso
    have h_rep : A335624_rep 273 := by use 0, 4, 1, 16; decide
    exact (A335624_eq_zero_iff_not_rep 273).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 274 := by use 0, 7, 15, 0; decide
    exact (A335624_eq_zero_iff_not_rep 274).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 275 := by use 0, 7, 1, 15; decide
    exact (A335624_eq_zero_iff_not_rep 275).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 276 := by use 0, 16, 4, 2; decide
    exact (A335624_eq_zero_iff_not_rep 276).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 277 := by use 0, 0, 9, 14; decide
    exact (A335624_eq_zero_iff_not_rep 277).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 278 := by use 0, 3, 10, 13; decide
    exact (A335624_eq_zero_iff_not_rep 278).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 279 := by use 2, 9, 5, 13; decide
    exact (A335624_eq_zero_iff_not_rep 279).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 280 := by use 4, 8, 2, 14; decide
    exact (A335624_eq_zero_iff_not_rep 280).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 281 := by use 0, 0, 16, 5; decide
    exact (A335624_eq_zero_iff_not_rep 281).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 282 := by use 1, 4, 3, 16; decide
    exact (A335624_eq_zero_iff_not_rep 282).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 283 := by use 0, 7, 15, 3; decide
    exact (A335624_eq_zero_iff_not_rep 283).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 284 := by use 1, 9, 9, 11; decide
    exact (A335624_eq_zero_iff_not_rep 284).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 285 := by use 0, 4, 13, 10; decide
    exact (A335624_eq_zero_iff_not_rep 285).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 286 := by use 1, 8, 14, 5; decide
    exact (A335624_eq_zero_iff_not_rep 286).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 287 := by use 1, 13, 6, 9; decide
    exact (A335624_eq_zero_iff_not_rep 287).mp h h_rep
  · exfalso; apply h16; decide
  · exfalso
    have h_rep : A335624_rep 289 := by use 0, 0, 0, 17; decide
    exact (A335624_eq_zero_iff_not_rep 289).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 290 := by use 0, 0, 1, 17; decide
    exact (A335624_eq_zero_iff_not_rep 290).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 291 := by use 1, 1, 0, 17; decide
    exact (A335624_eq_zero_iff_not_rep 291).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 292 := by use 0, 0, 16, 6; decide
    exact (A335624_eq_zero_iff_not_rep 292).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 293 := by use 0, 12, 7, 10; decide
    exact (A335624_eq_zero_iff_not_rep 293).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 294 := by use 0, 7, 7, 14; decide
    exact (A335624_eq_zero_iff_not_rep 294).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 295 := by use 2, 1, 1, 17; decide
    exact (A335624_eq_zero_iff_not_rep 295).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 296 := by use 4, 12, 6, 10; decide
    exact (A335624_eq_zero_iff_not_rep 296).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 297 := by use 0, 16, 4, 5; decide
    exact (A335624_eq_zero_iff_not_rep 297).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 298 := by use 0, 3, 0, 17; decide
    exact (A335624_eq_zero_iff_not_rep 298).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 299 := by use 0, 7, 15, 5; decide
    exact (A335624_eq_zero_iff_not_rep 299).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 300 := by use 1, 1, 3, 17; decide
    exact (A335624_eq_zero_iff_not_rep 300).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 301 := by use 0, 11, 12, 6; decide
    exact (A335624_eq_zero_iff_not_rep 301).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 302 := by use 1, 12, 11, 6; decide
    exact (A335624_eq_zero_iff_not_rep 302).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 303 := by use 1, 17, 3, 2; decide
    exact (A335624_eq_zero_iff_not_rep 303).mp h h_rep
  · exfalso; apply h16; decide
  · exfalso
    have h_rep : A335624_rep 305 := by use 0, 0, 4, 17; decide
    exact (A335624_eq_zero_iff_not_rep 305).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 306 := by use 0, 0, 9, 15; decide
    exact (A335624_eq_zero_iff_not_rep 306).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 307 := by use 0, 15, 1, 9; decide
    exact (A335624_eq_zero_iff_not_rep 307).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 308 := by use 0, 4, 6, 16; decide
    exact (A335624_eq_zero_iff_not_rep 308).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 309 := by use 2, 13, 10, 6; decide
    exact (A335624_eq_zero_iff_not_rep 309).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 310 := by use 0, 7, 15, 6; decide
    exact (A335624_eq_zero_iff_not_rep 310).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 311 := by use 1, 9, 2, 15; decide
    exact (A335624_eq_zero_iff_not_rep 311).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 312 := by use 2, 6, 4, 16; decide
    exact (A335624_eq_zero_iff_not_rep 312).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 313 := by use 0, 12, 0, 13; decide
    exact (A335624_eq_zero_iff_not_rep 313).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 314 := by use 0, 3, 4, 17; decide
    exact (A335624_eq_zero_iff_not_rep 314).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 315 := by use 0, 15, 9, 3; decide
    exact (A335624_eq_zero_iff_not_rep 315).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 316 := by use 6, 6, 10, 12; decide
    exact (A335624_eq_zero_iff_not_rep 316).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 317 := by use 3, 10, 12, 8; decide
    exact (A335624_eq_zero_iff_not_rep 317).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 318 := by use 2, 5, 8, 15; decide
    exact (A335624_eq_zero_iff_not_rep 318).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 319 := by use 2, 1, 5, 17; decide
    exact (A335624_eq_zero_iff_not_rep 319).mp h h_rep
  · exfalso; apply h16; decide
  · exfalso
    have h_rep : A335624_rep 321 := by use 0, 16, 4, 7; decide
    exact (A335624_eq_zero_iff_not_rep 321).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 322 := by use 0, 15, 9, 4; decide
    exact (A335624_eq_zero_iff_not_rep 322).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 323 := by use 0, 7, 7, 15; decide
    exact (A335624_eq_zero_iff_not_rep 323).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 324 := by use 0, 0, 0, 18; decide
    exact (A335624_eq_zero_iff_not_rep 324).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 325 := by use 0, 0, 1, 18; decide
    exact (A335624_eq_zero_iff_not_rep 325).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 326 := by use 0, 15, 1, 10; decide
    exact (A335624_eq_zero_iff_not_rep 326).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 327 := by use 1, 1, 15, 10; decide
    exact (A335624_eq_zero_iff_not_rep 327).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 328 := by use 8, 16, 2, 2; decide
    exact (A335624_eq_zero_iff_not_rep 328).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 329 := by use 0, 4, 13, 12; decide
    exact (A335624_eq_zero_iff_not_rep 329).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 330 := by use 1, 12, 11, 8; decide
    exact (A335624_eq_zero_iff_not_rep 330).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 331 := by use 0, 15, 9, 5; decide
    exact (A335624_eq_zero_iff_not_rep 331).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 332 := by use 1, 9, 9, 13; decide
    exact (A335624_eq_zero_iff_not_rep 332).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 333 := by use 0, 3, 0, 18; decide
    exact (A335624_eq_zero_iff_not_rep 333).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 334 := by use 0, 3, 10, 15; decide
    exact (A335624_eq_zero_iff_not_rep 334).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 335 := by use 1, 1, 3, 18; decide
    exact (A335624_eq_zero_iff_not_rep 335).mp h h_rep
  · exfalso; apply h16; decide
  · exfalso
    have h_rep : A335624_rep 337 := by use 0, 0, 9, 16; decide
    exact (A335624_eq_zero_iff_not_rep 337).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 338 := by use 0, 7, 15, 8; decide
    exact (A335624_eq_zero_iff_not_rep 338).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 339 := by use 0, 7, 1, 17; decide
    exact (A335624_eq_zero_iff_not_rep 339).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 340 := by use 0, 0, 4, 18; decide
    exact (A335624_eq_zero_iff_not_rep 340).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 341 := by use 0, 4, 1, 18; decide
    exact (A335624_eq_zero_iff_not_rep 341).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 342 := by use 0, 3, 18, 3; decide
    exact (A335624_eq_zero_iff_not_rep 342).mp h h_rep
  · exfalso
    have h_rep : A335624_rep 343 := by use 2, 17, 7, 1; decide
    exact (A335624_eq_zero_iff_not_rep 343).mp h h_rep
  · refine ⟨0, 43, by decide, by decide⟩
