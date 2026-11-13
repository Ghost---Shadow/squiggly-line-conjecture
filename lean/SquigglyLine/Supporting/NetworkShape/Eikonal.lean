/-
The distance field falls at rate exactly one.

`SignedDistance.lean` shows that the distance to the line changes by at most
one unit per unit moved. This file shows the bound is reached: walk from any
point straight to a nearest point of the line, and the distance falls by
exactly what you walk. So "slope at most one" cannot be improved, and a step
of sphere tracing along that path is as long as it can safely be.

Theorems: `infDist_toward_nearest`, `infDist_sub_infDist_toward_nearest`,
`exists_nearest_with_unit_rate`, `distanceField_toward_nearest`,
`not_lipschitzWith_infDist_of_lt_one`.
-/
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Tactic.Module
import SquigglyLine.Supporting.NetworkShape.SignedDistance

namespace SquigglyLine

open NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {S : Set E} {q p : E}

/-- **Rate exactly one.** On the straight path from `q` to a nearest point `p` of the set, a
fraction `t` of the way along, the distance to the set is the fraction `1 - t` of what it
was. -/
theorem infDist_toward_nearest (hp : p ∈ S) (hnear : Metric.infDist q S = dist q p)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Metric.infDist (q + t • (p - q)) S = (1 - t) * Metric.infDist q S := by
  have hstep : dist q (q + t • (p - q)) = t * dist q p := by
    rw [dist_eq_norm, dist_eq_norm,
      show q - (q + t • (p - q)) = t • (q - p) by module, norm_smul,
      Real.norm_of_nonneg ht0]
  have hleft : dist (q + t • (p - q)) p = (1 - t) * dist q p := by
    rw [dist_eq_norm, dist_eq_norm,
      show q + t • (p - q) - p = (1 - t) • (q - p) by module, norm_smul,
      Real.norm_of_nonneg (by linarith)]
  apply le_antisymm
  · -- `p` is still in the set, and it is `(1 - t)` of the old distance away.
    calc Metric.infDist (q + t • (p - q)) S
        ≤ dist (q + t • (p - q)) p := Metric.infDist_le_dist_of_mem hp
      _ = (1 - t) * Metric.infDist q S := by rw [hleft, hnear]
  · -- The distance cannot fall faster than one per unit walked.
    have h := Metric.infDist_le_infDist_add_dist (s := S) (x := q) (y := q + t • (p - q))
    rw [hstep, ← hnear] at h
    linarith

/-- The fall in distance equals the length walked. -/
theorem infDist_sub_infDist_toward_nearest (hp : p ∈ S)
    (hnear : Metric.infDist q S = dist q p) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Metric.infDist q S - Metric.infDist (q + t • (p - q)) S = dist q (q + t • (p - q)) := by
  have hstep : dist q (q + t • (p - q)) = t * dist q p := by
    rw [dist_eq_norm, dist_eq_norm,
      show q - (q + t • (p - q)) = t • (q - p) by module, norm_smul,
      Real.norm_of_nonneg ht0]
  rw [infDist_toward_nearest hp hnear ht0 ht1, hstep, hnear]
  ring

/-- In a space where closed balls are compact, every point has a nearest point of a closed
set, and the distance falls at rate one on the way to it. -/
theorem exists_nearest_with_unit_rate [ProperSpace E] (hS : IsClosed S) (hne : S.Nonempty)
    (q : E) :
    ∃ p ∈ S, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      Metric.infDist (q + t • (p - q)) S = (1 - t) * Metric.infDist q S := by
  obtain ⟨p, hp, hnear⟩ := hS.exists_infDist_eq_dist hne q
  exact ⟨p, hp, fun t ht0 ht1 => infDist_toward_nearest hp hnear ht0 ht1⟩

omit [NormedSpace ℝ E] in
/-- **The bound "slope at most one" cannot be improved.** If some point off the set has a
nearest point in it, the distance to the set has no slope limit below one. -/
theorem not_lipschitzWith_infDist_of_lt_one (hp : p ∈ S)
    (hnear : Metric.infDist q S = dist q p) (hq : 0 < dist q p) {K : ℝ≥0} (hK : K < 1) :
    ¬ LipschitzWith K (fun x => Metric.infDist x S) := by
  intro hlip
  -- Walk all the way to `p`: the distance falls from `dist q p` to zero.
  have h := hlip.dist_le_mul q p
  have hzero : Metric.infDist p S = 0 := Metric.infDist_zero_of_mem hp
  rw [Real.dist_eq, hzero, sub_zero, hnear, abs_of_pos hq] at h
  have hK' : (K : ℝ) < 1 := by exact_mod_cast hK
  nlinarith

section Line

variable {Inputs : Type*} [NormedAddCommGroup Inputs] [NormedSpace ℝ Inputs]
  {model : Model Inputs}

/-- **For the squiggly line.** From a point of space toward a nearest point of the line, the
distance field falls by exactly the distance walked. -/
theorem distanceField_toward_nearest {q p : Ambient Inputs} (hp : p ∈ GET_GRAPH model)
    (hnear : GET_DISTANCE_FIELD model q = dist q p) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    GET_DISTANCE_FIELD model (q + t • (p - q)) = (1 - t) * GET_DISTANCE_FIELD model q :=
  infDist_toward_nearest hp hnear ht0 ht1

end Line

end SquigglyLine
