/-
A chain of Markov chains.

Training a deep network is a chain through the training steps, each link of
which runs a chain through the layers. Both chains are memoryless: the next
state depends only on the current one.

The inner chain (`runLayers`), and what having no memory costs:
* `merged_stays_merged`  : two birds at the same place stay together;
* `card_image_runLayers_append_le` : the flock never spreads over more places;
* `dead_stays_dead`      : a state every layer fixes is never left.

The photon (`plateMatrix`), a two-state Markov chain with real chance in it:
* `plateMatrix_pow`      : after `n` plates it is alive with probability `c ^ n`
                           and "absorbed" is never left.

The outer chain (`gradientStep`), with orthogonal features:
* `TightFeatures.residual_iterate_gradientStep` : the error after `t` steps is
                           `(1 - η c) ^ t` times the error at the start;
* `TightFeatures.residual_gradientStep_inv`     : with `η = 1 / c`, one step fits.
-/
import Mathlib.LinearAlgebra.Matrix.Notation
import SquigglyLine.Kernel
import SquigglyLine.Polarizer
import SquigglyLine.ThreePolarizers

namespace SquigglyLine

/-! ### The inner chain: through the layers -/

section Inner

variable {α : Type*}

/-- Run a stack of layers. The head of the list is the first layer. -/
def runLayers : List (α → α) → α → α
  | [] => id
  | f :: rest => runLayers rest ∘ f

theorem runLayers_append (early late : List (α → α)) :
    runLayers (early ++ late) = runLayers late ∘ runLayers early := by
  induction early with
  | nil => rfl
  | cons f rest ih => simp only [List.cons_append, runLayers, ih, Function.comp_assoc]

/-- **Merged stays merged.** Two birds at the same place after some layers are at the same
place after any further layers. -/
theorem merged_stays_merged (early late : List (α → α)) {x y : α}
    (h : runLayers early x = runLayers early y) :
    runLayers (early ++ late) x = runLayers (early ++ late) y := by
  simp only [runLayers_append, Function.comp_apply, h]

/-- **The flock never spreads over more places.** Further layers cannot increase the number
of distinct places a flock occupies. -/
theorem card_image_runLayers_append_le [DecidableEq α] (early late : List (α → α))
    (flock : Finset α) :
    (flock.image (runLayers (early ++ late))).card ≤ (flock.image (runLayers early)).card := by
  rw [runLayers_append, ← Finset.image_image]
  exact Finset.card_image_le

/-- **Dead stays dead.** A state that every layer leaves alone is never left. -/
theorem dead_stays_dead (layers : List (α → α)) {dead : α} (h : ∀ f ∈ layers, f dead = dead) :
    runLayers layers dead = dead := by
  induction layers with
  | nil => rfl
  | cons f rest ih =>
    rw [runLayers, Function.comp_apply, h f (List.mem_cons_self ..)]
    exact ih fun g hg => h g (List.mem_cons_of_mem _ hg)

/-- A blocked photon stays blocked. -/
theorem polarizer_zero (φ : ℝ) : polarizer φ (0, 0) = (0, 0) := by
  simp [polarizer]

/-- A bird at the origin stays at the origin under any fan. -/
theorem fan_zero (θ : ℝ) : fan θ (0, 0) = (0, 0) := by
  simp [fan, rotate, relu2]

end Inner

/-! ### The photon: a two-state Markov chain -/

section Photon

/-- The transition matrix of one plate. State 0 is "alive", state 1 is "absorbed". An alive
photon passes with probability `c`. -/
def plateMatrix (c : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![c, 1 - c; 0, 1]

/-- Each row of the transition matrix is a probability distribution. -/
theorem plateMatrix_row_sum (c : ℝ) (i : Fin 2) : ∑ j, plateMatrix c i j = 1 := by
  fin_cases i <;> simp [plateMatrix, Fin.sum_univ_two]

/-- **The photon's chain.** After `n` plates an alive photon is still alive with probability
`c ^ n`, and an absorbed photon is still absorbed. -/
theorem plateMatrix_pow (c : ℝ) (n : ℕ) :
    plateMatrix c ^ n = !![c ^ n, 1 - c ^ n; 0, 1] := by
  induction n with
  | zero => simp [Matrix.one_fin_two]
  | succ n ih =>
    rw [pow_succ, ih, plateMatrix, Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [pow_succ]
    ring

/-- The survival probability is the square of the surviving length: `(cos² θ) ^ n` is
`(cos θ ^ n)²`. -/
theorem survival_eq_sq_length (θ : ℝ) (n : ℕ) :
    (plateMatrix (Real.cos θ ^ 2) ^ n) 0 0 = (Real.cos θ ^ n) ^ 2 := by
  rw [plateMatrix_pow]
  simp [pow_right_comm]

end Photon

/-! ### The outer chain: through training -/

section Outer

open ContinuousLinearMap

variable {Θ Y : Type*}
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  {A : Θ →L[ℝ] Y} {c : ℝ}

/-- **The outer chain, solved.** With orthogonal features of squared length `c`, the error
after `t` gradient steps is `(1 - η c) ^ t` times the error at the start. -/
theorem TightFeatures.residual_iterate_gradientStep (h : TightFeatures A c) (y : Y) (η : ℝ)
    (θ : Θ) (t : ℕ) :
    residual (A : Θ →ₗ[ℝ] Y) y ((gradientStep A y η)^[t] θ)
      = (1 - η * c) ^ t • residual (A : Θ →ₗ[ℝ] Y) y θ := by
  induction t with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', residual_gradientStep, ih, h]
    module

/-- **One step fits.** With the step size `1 / c`, a single gradient step leaves no error. -/
theorem TightFeatures.residual_gradientStep_inv (h : TightFeatures A c) (hc : c ≠ 0) (y : Y)
    (θ : Θ) : residual (A : Θ →ₗ[ℝ] Y) y (gradientStep A y c⁻¹ θ) = 0 := by
  have := h.residual_iterate_gradientStep y c⁻¹ θ 1
  simpa [inv_mul_cancel₀ hc] using this

end Outer

end SquigglyLine
