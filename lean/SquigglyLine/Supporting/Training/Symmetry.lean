/-
Symmetries: changes to the weights that leave the line alone.

When a change to the weights does not change the function, the loss has no
slope in that direction, and training moves at right angles to it. Three
cases, each a well-known fact about real networks.

Rescaling everything (weights that feed a normalisation):
* `inner_gradient_self_eq_zero` : if the loss does not change when the weights
  are rescaled, the gradient is at right angles to the weights.
* `norm_sq_sub_smul_of_inner_eq_zero` : so a gradient step adds `η² ‖g‖²` to
  the squared size of the weights.
* `norm_le_norm_sub_smul` : the weights never get shorter.

Rescaling one layer against the next (two weights multiplied, `a * b`):
* `balance_after_step` : a gradient step changes `a² - b²` only by a factor
  `1 - η² (a b - y)²`.
* `balanced_stays_balanced` : layers of equal size stay of equal size.
* `abs_eq_abs_of_balanced` : and then each carries the same share of the
  slope.

Relabelling the hidden units:
* `oneHiddenLayer_relabel` : shuffling the units of a hidden layer gives the
  same function.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic

namespace SquigglyLine

open Topology

/-! ### Rescaling everything -/

section Scale

variable {Θ : Type*} [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ]

/-- A loss that does not change when all the weights are multiplied by a positive number. The
weights that feed a normalisation layer are like this. -/
def ScaleInvariant (L : Θ → ℝ) : Prop :=
  ∀ c : ℝ, 0 < c → ∀ θ, L (c • θ) = L θ

/-- **The gradient is at right angles to the weights.** Here `g` is the gradient of `L` at `θ`,
in the sense that the loss changes at the rate `⟪g, θ⟫` when the weights move along
themselves. -/
theorem inner_gradient_self_eq_zero {L : Θ → ℝ} (hL : ScaleInvariant L) {θ g : Θ}
    (hgrad : HasDerivAt (fun s : ℝ => L (θ + s • θ)) (inner ℝ g θ) 0) : inner ℝ g θ = 0 := by
  have hconst : (fun _ : ℝ => L θ) =ᶠ[𝓝 0] fun s => L (θ + s • θ) := by
    filter_upwards [Ioi_mem_nhds (show (-1 : ℝ) < 0 by norm_num)] with s hs
    rw [show θ + s • θ = (1 + s) • θ by rw [add_smul, one_smul]]
    exact (hL (1 + s) (by linarith [Set.mem_Ioi.mp hs]) θ).symm
  exact (hgrad.congr_of_eventuallyEq hconst).unique (hasDerivAt_const 0 (L θ))

/-- **A step at right angles makes the weights longer.** -/
theorem norm_sq_sub_smul_of_inner_eq_zero {θ g : Θ} (h : inner ℝ g θ = 0) (η : ℝ) :
    ‖θ - η • g‖ ^ 2 = ‖θ‖ ^ 2 + η ^ 2 * ‖g‖ ^ 2 := by
  rw [norm_sub_sq_real, inner_smul_right, real_inner_comm g θ, h, norm_smul, mul_pow,
    Real.norm_eq_abs, sq_abs]
  ring

/-- With such a loss, gradient descent never shortens the weights. -/
theorem norm_le_norm_sub_smul {θ g : Θ} (h : inner ℝ g θ = 0) (η : ℝ) :
    ‖θ‖ ≤ ‖θ - η • g‖ := by
  refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_
  rw [norm_sq_sub_smul_of_inner_eq_zero h]
  exact le_add_of_nonneg_right (by positivity)

end Scale

/-! ### Rescaling one layer against the next -/

section Balance

/-- **Training keeps the layers in balance.** The model is `a * b` and the loss is
`(a b - y)² / 2`. One gradient step changes `a² - b²` only at second order in the step. -/
theorem balance_after_step (a b y η : ℝ) :
    (a - η * ((a * b - y) * b)) ^ 2 - (b - η * ((a * b - y) * a)) ^ 2
      = (a ^ 2 - b ^ 2) * (1 - η ^ 2 * (a * b - y) ^ 2) := by
  ring

/-- Two layers of equal size are still of equal size after a step. -/
theorem balanced_stays_balanced (a b y η : ℝ) (h : a ^ 2 = b ^ 2) :
    (a - η * ((a * b - y) * b)) ^ 2 = (b - η * ((a * b - y) * a)) ^ 2 := by
  have hstep := balance_after_step a b y η
  rw [h, sub_self, zero_mul] at hstep
  exact sub_eq_zero.mp hstep

/-- Balanced layers have the same size, so each carries the same share of the slope `a * b`. -/
theorem abs_eq_abs_of_balanced {a b : ℝ} (h : a ^ 2 = b ^ 2) : |a| = |b| :=
  (sq_eq_sq_iff_abs_eq_abs a b).mp h

end Balance

/-! ### Relabelling the hidden units -/

section Relabel

variable {ι X : Type*} [Fintype ι]

/-- A network with one hidden layer. Unit `i` reads the input through `w i`, applies the
activation, and is weighted by `a i` on the way out. -/
def oneHiddenLayer (act : ℝ → ℝ) (w : ι → X → ℝ) (a : ι → ℝ) (x : X) : ℝ :=
  ∑ i, a i * act (w i x)

/-- **Shuffling the hidden units gives the same function.** -/
theorem oneHiddenLayer_relabel (act : ℝ → ℝ) (w : ι → X → ℝ) (a : ι → ℝ) (π : Equiv.Perm ι) :
    oneHiddenLayer act (w ∘ π) (a ∘ π) = oneHiddenLayer act w a := by
  funext x
  exact Equiv.sum_comp π fun i => a i * act (w i x)

end Relabel

end SquigglyLine
