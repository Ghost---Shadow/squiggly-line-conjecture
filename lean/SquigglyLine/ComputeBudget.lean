/-
Chinchilla: how to split a compute budget.

The loss above the floor is `A / N + B / D`, with `N` parameters and `D` data.
The budget fixes `N * D`.

* `four_mul_div_le_sq` : for any split, the loss above the floor squared is at
  least `4 A B / (N D)`.
* `balanced_loss_sq` : a split with `A / N = B / D` reaches that bound.
* `balanced_is_optimal` : so no split with the same budget does better.
* `balanced_ratio` : at the best split `N / D = A / B`, whatever the budget.
* `balanced_scale` : scaling parameters and data by the same factor keeps the
  split balanced.
* `chinchilla_optimal` : the same with the floor added.
* `balanced_is_optimal_rpow` : the same when both terms fall as a common
  power of their size.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace SquigglyLine

variable {A B N D N₀ D₀ : ℝ}

/-- **A sum with a fixed product.** For any split of the budget, the loss above the floor
squared is at least `4 A B / (N D)`. -/
theorem four_mul_div_le_sq (A B N D : ℝ) : 4 * (A * B / (N * D)) ≤ (A / N + B / D) ^ 2 :=
  calc 4 * (A * B / (N * D)) = 4 * (A / N) * (B / D) := by
        rw [← div_mul_div_comm, mul_assoc]
    _ ≤ (A / N + B / D) ^ 2 := four_mul_le_sq_add _ _

/-- **What the best split buys.** With the two terms balanced, the loss above the floor
squared is `4 A B` over the budget. -/
theorem balanced_loss_sq (hbal : A / N₀ = B / D₀) :
    (A / N₀ + B / D₀) ^ 2 = 4 * (A * B / (N₀ * D₀)) := by
  rw [← div_mul_div_comm, ← hbal]
  ring

/-- **The best split balances the two terms.** If `A / N₀ = B / D₀`, no other split with
the same budget has a smaller loss. -/
theorem balanced_is_optimal (hA : 0 ≤ A) (hB : 0 ≤ B) (hN₀ : 0 < N₀) (hD₀ : 0 < D₀)
    (hN : 0 < N) (hD : 0 < D) (hbal : A / N₀ = B / D₀) (hbudget : N₀ * D₀ = N * D) :
    A / N₀ + B / D₀ ≤ A / N + B / D := by
  have hbest : 0 ≤ A / N₀ + B / D₀ := add_nonneg (div_nonneg hA hN₀.le) (div_nonneg hB hD₀.le)
  have hother : 0 ≤ A / N + B / D := add_nonneg (div_nonneg hA hN.le) (div_nonneg hB hD.le)
  refine (sq_le_sq₀ hbest hother).mp ?_
  calc (A / N₀ + B / D₀) ^ 2 = 4 * (A * B / (N₀ * D₀)) := balanced_loss_sq hbal
    _ = 4 * (A * B / (N * D)) := by rw [hbudget]
    _ ≤ (A / N + B / D) ^ 2 := four_mul_div_le_sq A B N D

/-- **A fixed ratio.** At the best split, parameters over data is `A / B`, whatever the
budget. -/
theorem balanced_ratio (hB : B ≠ 0) (hN₀ : N₀ ≠ 0) (hD₀ : D₀ ≠ 0) (hbal : A / N₀ = B / D₀) :
    N₀ / D₀ = A / B := by
  rw [div_eq_div_iff hN₀ hD₀] at hbal
  rw [div_eq_div_iff hD₀ hB]
  linarith

/-- **They grow together.** Scaling parameters and data by the same factor keeps the split
balanced. -/
theorem balanced_scale (s : ℝ) (hbal : A / N₀ = B / D₀) : A / (s * N₀) = B / (s * D₀) := by
  rw [mul_comm s N₀, mul_comm s D₀, ← div_div, ← div_div, hbal]

/-- **With the floor.** The whole loss `E + A / N + B / D` is smallest at the balanced
split. -/
theorem chinchilla_optimal (E : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hN₀ : 0 < N₀) (hD₀ : 0 < D₀)
    (hN : 0 < N) (hD : 0 < D) (hbal : A / N₀ = B / D₀) (hbudget : N₀ * D₀ = N * D) :
    E + A / N₀ + B / D₀ ≤ E + A / N + B / D := by
  linarith [balanced_is_optimal hA hB hN₀ hD₀ hN hD hbal hbudget]

/-- **Any common power.** The same holds when both terms fall as the same power `a` of
their size. -/
theorem balanced_is_optimal_rpow (a : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hN₀ : 0 < N₀)
    (hD₀ : 0 < D₀) (hN : 0 < N) (hD : 0 < D) (hbal : A / N₀ ^ a = B / D₀ ^ a)
    (hbudget : N₀ * D₀ = N * D) :
    A / N₀ ^ a + B / D₀ ^ a ≤ A / N ^ a + B / D ^ a :=
  balanced_is_optimal hA hB (Real.rpow_pos_of_pos hN₀ a) (Real.rpow_pos_of_pos hD₀ a)
    (Real.rpow_pos_of_pos hN a) (Real.rpow_pos_of_pos hD a) hbal
    (by rw [← Real.mul_rpow hN₀.le hD₀.le, ← Real.mul_rpow hN.le hD.le, hbudget])

end SquigglyLine
