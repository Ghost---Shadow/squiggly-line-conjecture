/-
The tunnel that cannot turn.

A ReLU network with one neuron per layer,

    relu (w₁ * relu (w₂ * relu (w₃ * x + b₃) + b₂) + b₁),

never turns, at any depth: its output only rises with the input, or only
falls. Each layer is monotone, and a chain of monotone maps is monotone.
In one dimension the only rotation is the full flip, so there is nothing to
turn through.
-/
import Mathlib.Analysis.Normed.Module.Basic

namespace SquigglyLine

/-- A layer with a single neuron: `h ↦ relu (w * h + b)`. -/
def APPLY_NARROW_LAYER (w b : ℝ) (h : ℝ) : ℝ :=
  max (w * h + b) 0

/-- A network with one neuron per layer. The head of the list is the last layer. -/
def RUN_NARROW_CHAIN : List (ℝ × ℝ) → ℝ → ℝ
  | [] => id
  | layer :: rest => APPLY_NARROW_LAYER layer.1 layer.2 ∘ RUN_NARROW_CHAIN rest

/-- A function that never turns: it only rises, or it only falls. -/
def NEVER_TURNS (f : ℝ → ℝ) : Prop :=
  Monotone f ∨ Antitone f

theorem narrowLayer_neverTurns (w b : ℝ) : NEVER_TURNS (APPLY_NARROW_LAYER w b) :=
  (le_total 0 w).elim
    (fun hw => .inl fun _ _ hxy =>
      max_le_max (add_le_add_left (mul_le_mul_of_nonneg_left hxy hw) b) le_rfl)
    (fun hw => .inr fun _ _ hxy =>
      max_le_max (add_le_add_left (mul_le_mul_of_nonpos_left hxy hw) b) le_rfl)

/-- Chaining two functions that never turn gives a function that never turns. -/
theorem NEVER_TURNS.comp {f g : ℝ → ℝ} (hf : NEVER_TURNS f) (hg : NEVER_TURNS g) :
    NEVER_TURNS (f ∘ g) := by
  rcases hf with hf | hf <;> rcases hg with hg | hg
  · exact .inl (hf.comp hg)
  · exact .inr (hf.comp_antitone hg)
  · exact .inr (hf.comp_monotone hg)
  · exact .inl (hf.comp hg)

/-- **A one-neuron-per-layer network never turns**, whatever its depth and weights. -/
theorem narrowChain_neverTurns (layers : List (ℝ × ℝ)) : NEVER_TURNS (RUN_NARROW_CHAIN layers) := by
  induction layers with
  | nil => exact .inl monotone_id
  | cons layer rest ih => exact (narrowLayer_neverTurns layer.1 layer.2).comp ih

/-- What "never turns" means for three inputs in a row: the middle output lies between the
outer two. There is no peak and no valley. -/
theorem NEVER_TURNS.between {f : ℝ → ℝ} (hf : NEVER_TURNS f) {x y z : ℝ} (hxy : x ≤ y)
    (hyz : y ≤ z) : min (f x) (f z) ≤ f y ∧ f y ≤ max (f x) (f z) := by
  rcases hf with hf | hf
  · exact ⟨(min_le_left _ _).trans (hf hxy), (hf hyz).trans (le_max_right _ _)⟩
  · exact ⟨(min_le_right _ _).trans (hf hyz), (hf hxy).trans (le_max_left _ _)⟩

end SquigglyLine
