import FormalConjecturesUtil

/-!
# Erdős Problem 508

*Reference:* [erdosproblems.com/508](https://www.erdosproblems.com/508)

proven by considering the [Moser-Spindel graph]
or the [Golomb graph]
*At least 4 colors are required:* [Moser-Spindel graph](https://de.wikipedia.org/wiki/Moser-Spindel)
*At least 4 colors are required:* [Golomb graph](https://en.wikipedia.org/wiki/Golomb_graph)
*At least 5 colors are required:* [de Grey 2018](https://arxiv.org/abs/1804.02385)
-/

open SimpleGraph
open scoped EuclideanGeometry

namespace Erdos508

scoped notation "χ(ℝ²)" => SimpleGraph.chromaticNumber (UnitDistancePlaneGraph Set.univ)

/--
The Hadwiger–Nelson problem asks: How many colors are required to color the plane
such that no two points at distance 1 from each other have the same color?
-/
theorem HadwigerNelsonProblem.eq7 :
    χ(ℝ²) = 7 := by
  sorry

end Erdos508

theorem Erdos508.HadwigerNelsonProblem.eq7.disproof : ¬ (type_of% @Erdos508.HadwigerNelsonProblem.eq7) := sorry
