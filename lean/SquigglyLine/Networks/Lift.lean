/-
Squiggly below, flat above: the kernel trick.

A model that is linear in its weights first lifts the input `x` to a feature
vector `φ x`, usually in a space of many more dimensions, and then takes the
inner product with its weights `θ`. Upstairs, in the feature space, the model
is a flat plane. Downstairs it is a squiggly line.

* `liftedModel_eq_comp` : the model is the flat function after the lift.
* `flatModel_blend` : the function upstairs is flat.
* `embed_mem_curve_liftedModel_iff` : a point is on the squiggly line exactly
  when its lift is on the flat plane.
* `boundary_eq_preimage` : the same for the boundary of a classifier.
* `abs_liftedModel_sub_le`, `lipschitzWith_liftedModel` : the slope of the
  line is at most the tilt of the plane times the stretch of the lift.
* `verticalDist_liftedModel_le` : so the slope sandwich reads in those two.
* `liftedModel_add_sum` : **the kernel trick.** Weights moved along the
  lifted data predict through the kernel alone.
* `liftKernel_comm`, `sum_sum_liftKernel_nonneg` : such a kernel is symmetric
  and never negative.
* `exists_lift_eq` : any function is flat in some lift, so the statement says
  something only when the lift is fixed in advance.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import SquigglyLine.Theorem.Sandwich

namespace SquigglyLine

open NNReal

variable {X Θ : Type*} [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ]

/-- The flat function upstairs: the inner product of a feature vector with the weights. -/
def EVALUATE_FLAT_MODEL (θ v : Θ) : ℝ :=
  inner ℝ θ v

/-- A model linear in its weights: lift the input, then apply the flat function. -/
def EVALUATE_LIFTED_MODEL (φ : X → Θ) (θ : Θ) (x : X) : ℝ :=
  inner ℝ θ (φ x)

/-- The kernel of a lift: how much two inputs overlap upstairs. -/
def GET_LIFT_KERNEL (φ : X → Θ) (x x' : X) : ℝ :=
  inner ℝ (φ x) (φ x')

/-! ### Flat above, squiggly below -/

section Flat

variable (φ : X → Θ) (θ : Θ)

theorem liftedModel_eq_comp : EVALUATE_LIFTED_MODEL φ θ = EVALUATE_FLAT_MODEL θ ∘ φ :=
  rfl

/-- **Flat above.** Upstairs, the value at a blend of two feature vectors is the same blend
of the two values. -/
theorem flatModel_blend (v w : Θ) (t : ℝ) :
    EVALUATE_FLAT_MODEL θ ((1 - t) • v + t • w) = (1 - t) * EVALUATE_FLAT_MODEL θ v + t * EVALUATE_FLAT_MODEL θ w := by
  simp only [EVALUATE_FLAT_MODEL, inner_add_right, inner_smul_right]

/-- **The squiggly line is the flat plane, seen through the lift.** A point is on the line
downstairs exactly when its lift is on the plane upstairs. -/
theorem embed_mem_curve_liftedModel_iff (p : DataPoint X) :
    EMBED_DATA_POINT p ∈ GET_GRAPH (EVALUATE_LIFTED_MODEL φ θ) ↔ EMBED_DATA_POINT (φ p.1, p.2) ∈ GET_GRAPH (EVALUATE_FLAT_MODEL θ) := by
  rw [propext (embed_mem_curve_iff _ _), propext (embed_mem_curve_iff _ _)]
  rfl

/-- **A squiggly boundary is a flat one upstairs.** The inputs a classifier scores zero are
the ones whose lifts lie on a flat plane through the origin. -/
theorem boundary_eq_preimage :
    {x | EVALUATE_LIFTED_MODEL φ θ x = 0} = φ ⁻¹' {v | EVALUATE_FLAT_MODEL θ v = 0} :=
  rfl

end Flat

/-! ### Where the squiggle is -/

section Slope

/-- The line changes by at most the size of the weights times how far the lift moves. -/
theorem abs_liftedModel_sub_le (φ : X → Θ) (θ : Θ) (x x' : X) :
    |EVALUATE_LIFTED_MODEL φ θ x - EVALUATE_LIFTED_MODEL φ θ x'| ≤ ‖θ‖ * ‖φ x - φ x'‖ := by
  rw [EVALUATE_LIFTED_MODEL, EVALUATE_LIFTED_MODEL, ← inner_sub_right]
  exact abs_real_inner_le_norm _ _

/-- **Slope is tilt times stretch.** If the lift stretches distances by at most `K`, the
line is no steeper than the size of the weights times `K`. -/
theorem lipschitzWith_liftedModel [PseudoMetricSpace X] {φ : X → Θ} {K : ℝ≥0}
    (hφ : LipschitzWith K φ) (θ : Θ) : LipschitzWith (‖θ‖₊ * K) (EVALUATE_LIFTED_MODEL φ θ) :=
  LipschitzWith.of_dist_le_mul fun x x' => by
    have hstretch : ‖φ x - φ x'‖ ≤ K * dist x x' := dist_eq_norm (φ x) (φ x') ▸ hφ.dist_le_mul x x'
    rw [Real.dist_eq, NNReal.coe_mul, coe_nnnorm, mul_assoc]
    exact (abs_liftedModel_sub_le φ θ x x').trans
      (mul_le_mul_of_nonneg_left hstretch (norm_nonneg θ))

/-- **The sandwich, in tilt and stretch.** The line can be nearer to a data point than its
vertical error only by the factor `√(1 + (‖θ‖ K)²)`. -/
theorem verticalDist_liftedModel_le {X : Type*} [SeminormedAddCommGroup X] {φ : X → Θ}
    {K : ℝ≥0} (hφ : LipschitzWith K φ) (θ : Θ) (p : DataPoint X) :
    GET_VERTICAL_ERROR (EVALUATE_LIFTED_MODEL φ θ) p
      ≤ √(1 + (‖θ‖ * K) ^ 2) * GET_NEAREST_DISTANCE (EVALUATE_LIFTED_MODEL φ θ) p := by
  simpa using verticalDist_le_of_lipschitz (lipschitzWith_liftedModel hφ θ) p

end Slope

/-! ### The kernel trick -/

section Kernel

variable {ι : Type*} (φ : X → Θ)

/-- **The kernel trick.** Move the weights from `θ₀` along the lifted data points, by `c i`
along the lift of `xs i`. The new prediction at any input is the old one plus the kernel
between that input and each data point, weighted by `c`. The lift itself is never needed. -/
theorem liftedModel_add_sum (s : Finset ι) (θ₀ : Θ) (xs : ι → X) (c : ι → ℝ) (x : X) :
    EVALUATE_LIFTED_MODEL φ (θ₀ + ∑ i ∈ s, c i • φ (xs i)) x
      = EVALUATE_LIFTED_MODEL φ θ₀ x + ∑ i ∈ s, c i * GET_LIFT_KERNEL φ (xs i) x := by
  simp only [EVALUATE_LIFTED_MODEL, GET_LIFT_KERNEL, inner_add_left, sum_inner, inner_smul_left]
  rfl

/-- The kernel does not care which input comes first. -/
theorem liftKernel_comm (x x' : X) : GET_LIFT_KERNEL φ x x' = GET_LIFT_KERNEL φ x' x :=
  real_inner_comm _ _

/-- **A kernel from a lift is never negative.** Weigh the data points by any numbers `c`. The
kernel summed over all pairs with those weights is the squared length of one vector
upstairs. -/
theorem sum_sum_liftKernel_eq (s : Finset ι) (xs : ι → X) (c : ι → ℝ) :
    ∑ i ∈ s, ∑ j ∈ s, c i * c j * GET_LIFT_KERNEL φ (xs i) (xs j) = ‖∑ i ∈ s, c i • φ (xs i)‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [inner_smul_left, inner_smul_right, GET_LIFT_KERNEL]
  simp only [conj_trivial]
  ring

theorem sum_sum_liftKernel_nonneg (s : Finset ι) (xs : ι → X) (c : ι → ℝ) :
    0 ≤ ∑ i ∈ s, ∑ j ∈ s, c i * c j * GET_LIFT_KERNEL φ (xs i) (xs j) := by
  rw [sum_sum_liftKernel_eq]
  positivity

end Kernel

/-! ### The catch -/

/-- **Any function is flat in some lift.** Take the function itself as the lift. So "flat
upstairs" says something only when the lift is chosen before the labels are seen. -/
theorem exists_lift_eq {X : Type*} (f : X → ℝ) : ∃ φ : X → ℝ, EVALUATE_LIFTED_MODEL φ 1 = f :=
  ⟨f, by
    funext x
    simp [EVALUATE_LIFTED_MODEL]⟩

end SquigglyLine
