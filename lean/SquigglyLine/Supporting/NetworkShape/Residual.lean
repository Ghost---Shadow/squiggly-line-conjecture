/-
Residual layers: what a skip does to squiggle.

A residual layer is `x + branch x`. If the branch has slope at most `K`, the
layer has slope between `1 - K` and `1 + K`. Three things follow.

* With `K < 1` no two inputs are merged, and with one input the layer is
  always rising: a residual layer adds a turn only where its branch is
  steeper than one.
* `L` layers with branches of slope `c / L` have total slope at most `e ^ c`,
  however deep.
* The memory cell of an LSTM is a skip through time with a gate on it: its
  slope per step is the forget gate, and exactly one with the gate open.

Written in typical Mathlib style; waiting to be ported to `STYLE.md`.

Definitions: `ADD_SKIP`, `RUN_RESIDUAL_LAYERS`, `UPDATE_CELL`, `RUN_CELL`.

Theorems: `lipschitzWith_addSkip`, `le_dist_addSkip`, `addSkip_injective`,
`strictMono_addSkip`, `neverTurns_addSkip`, `one_add_div_pow_le_exp`,
`lipschitzWith_runResidualLayers`, `dist_runResidualLayers_le_exp`,
`abs_updateCell_sub`, `abs_updateCell_sub_le`, `updateCell_sub_of_open_gate`,
`runCell_sub`.
-/
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.MetricSpace.Lipschitz
import SquigglyLine.Networks.NarrowChain

namespace SquigglyLine

open NNReal

variable {E : Type*} [NormedAddCommGroup E] {branch : E → E} {K : ℝ≥0}

/-- A residual layer: the input, plus what the branch makes of it.
Python: `x + branch(x)`. -/
def ADD_SKIP (branch : E → E) (x : E) : E :=
  x + branch x

/-- A residual layer is no steeper than one plus its branch. -/
theorem lipschitzWith_addSkip (h : LipschitzWith K branch) :
    LipschitzWith (1 + K) (ADD_SKIP branch) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  have hb := h.dist_le_mul x y
  calc dist (x + branch x) (y + branch y)
      ≤ dist x y + dist (branch x) (branch y) := dist_add_add_le _ _ _ _
    _ ≤ dist x y + K * dist x y := by gcongr
    _ = ((1 + K : ℝ≥0) : ℝ) * dist x y := by push_cast; ring

/-- **A skip keeps points apart.** Two outputs are at least `1 - K` of the distance between
their inputs. -/
theorem le_dist_addSkip (h : LipschitzWith K branch) (x y : E) :
    (1 - K) * dist x y ≤ dist (ADD_SKIP branch x) (ADD_SKIP branch y) := by
  have h1 := norm_sub_norm_le (x - y) (branch y - branch x)
  have h2 : x - y - (branch y - branch x) = x + branch x - (y + branch y) := by abel
  have h3 : ‖branch y - branch x‖ ≤ K * ‖x - y‖ := by
    have := h.dist_le_mul y x
    rwa [dist_eq_norm, dist_eq_norm, norm_sub_rev y x] at this
  rw [h2] at h1
  simp only [ADD_SKIP, dist_eq_norm]
  linarith

/-- With a branch of slope below one, a residual layer never merges two inputs. -/
theorem addSkip_injective (h : LipschitzWith K branch) (hK : K < 1) :
    Function.Injective (ADD_SKIP branch) := by
  intro x y hxy
  have hle := le_dist_addSkip h x y
  rw [hxy, dist_self] at hle
  have hK' : (K : ℝ) < 1 := by exact_mod_cast hK
  have hd : dist x y ≤ 0 := by nlinarith [dist_nonneg (x := x) (y := y)]
  exact dist_le_zero.mp hd

/-- With one input and a branch of slope below one, a residual layer is always rising. -/
theorem strictMono_addSkip {branch : ℝ → ℝ} (h : LipschitzWith K branch) (hK : K < 1) :
    StrictMono (ADD_SKIP branch) := by
  intro x y hxy
  have hb := h.dist_le_mul x y
  rw [Real.dist_eq, Real.dist_eq, abs_of_neg (sub_neg.mpr hxy)] at hb
  have hle : branch x - branch y ≤ |branch x - branch y| := le_abs_self _
  have hK' : (K : ℝ) < 1 := by exact_mod_cast hK
  have hlt : (K : ℝ) * (y - x) < 1 * (y - x) :=
    mul_lt_mul_of_pos_right hK' (sub_pos.mpr hxy)
  show x + branch x < y + branch y
  linarith

/-- **A turn has to be bought in the branch.** With a branch of slope below one, a residual
layer never turns. -/
theorem neverTurns_addSkip {branch : ℝ → ℝ} (h : LipschitzWith K branch) (hK : K < 1) :
    NEVER_TURNS (ADD_SKIP branch) :=
  Or.inl (strictMono_addSkip h hK).monotone

/-- `(1 + c / L) ^ L` never passes `e ^ c`. -/
theorem one_add_div_pow_le_exp {c : ℝ} (hc : 0 ≤ c) (L : ℕ) :
    (1 + c / L) ^ L ≤ Real.exp c := by
  rcases Nat.eq_zero_or_pos L with rfl | hL
  · simpa using Real.one_le_exp hc
  · have hdiv : 0 ≤ c / L := div_nonneg hc (Nat.cast_nonneg L)
    have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
    calc (1 + c / L) ^ L
        ≤ (Real.exp (c / L)) ^ L :=
          pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp (c / L)]) L
      _ = Real.exp c := by
          rw [← Real.exp_nat_mul]
          congr 1
          field_simp

/-- A stack of residual layers: layer `n` adds `branches n` of what the layers below made.
Python: `for n in range(L): x = x + branches[n](x)`. -/
def RUN_RESIDUAL_LAYERS (branches : ℕ → E → E) : ℕ → E → E
  | 0 => id
  | n + 1 => ADD_SKIP (branches n) ∘ RUN_RESIDUAL_LAYERS branches n

/-- `L` residual layers with branches of slope at most `K` have slope at most `(1 + K) ^ L`. -/
theorem lipschitzWith_runResidualLayers {branches : ℕ → E → E}
    (h : ∀ n, LipschitzWith K (branches n)) (L : ℕ) :
    LipschitzWith ((1 + K) ^ L) (RUN_RESIDUAL_LAYERS branches L) := by
  induction L with
  | zero => simpa [RUN_RESIDUAL_LAYERS] using LipschitzWith.id
  | succ n ih =>
    have hcomp := (lipschitzWith_addSkip (h n)).comp ih
    rwa [← pow_succ'] at hcomp

/-- **Depth does not blow up the slope.** If each of `L` branches has slope at most `c / L`,
the whole stack has slope at most `e ^ c`, whatever `L` is. -/
theorem dist_runResidualLayers_le_exp {branches : ℕ → E → E} {c : ℝ≥0} {L : ℕ}
    (h : ∀ n, LipschitzWith (c / L) (branches n)) (x y : E) :
    dist (RUN_RESIDUAL_LAYERS branches L x) (RUN_RESIDUAL_LAYERS branches L y)
      ≤ Real.exp c * dist x y := by
  have hlip := (lipschitzWith_runResidualLayers h L).dist_le_mul x y
  have hbound : (((1 + c / L : ℝ≥0) ^ L : ℝ≥0) : ℝ) ≤ Real.exp c := by
    push_cast
    exact one_add_div_pow_le_exp c.coe_nonneg L
  exact hlip.trans (mul_le_mul_of_nonneg_right hbound dist_nonneg)

/-- One step of the memory cell of an LSTM: keep the share `f` of the cell, and add the share
`i` of the candidate `g`.
Python: `f * cell + i * g`. -/
def UPDATE_CELL (f i g cell : ℝ) : ℝ :=
  f * cell + i * g

/-- **The slope of the cell is the forget gate.** -/
theorem abs_updateCell_sub {f : ℝ} (hf : 0 ≤ f) (i g c₁ c₂ : ℝ) :
    |UPDATE_CELL f i g c₁ - UPDATE_CELL f i g c₂| = f * |c₁ - c₂| := by
  rw [UPDATE_CELL, UPDATE_CELL, show f * c₁ + i * g - (f * c₂ + i * g) = f * (c₁ - c₂) by ring,
    abs_mul, abs_of_nonneg hf]

/-- A gate between zero and one never makes two memories differ by more. -/
theorem abs_updateCell_sub_le {f : ℝ} (hf0 : 0 ≤ f) (hf1 : f ≤ 1) (i g c₁ c₂ : ℝ) :
    |UPDATE_CELL f i g c₁ - UPDATE_CELL f i g c₂| ≤ |c₁ - c₂| := by
  rw [abs_updateCell_sub hf0]
  exact mul_le_of_le_one_left (abs_nonneg _) hf1

/-- **With the gate open the cell is a skip through time.** The difference between two
memories is carried forward unchanged. -/
theorem updateCell_sub_of_open_gate (i g c₁ c₂ : ℝ) :
    UPDATE_CELL 1 i g c₁ - UPDATE_CELL 1 i g c₂ = c₁ - c₂ := by
  rw [UPDATE_CELL, UPDATE_CELL]
  ring

/-- The cell after `n` steps, with the gates and candidates of each step given. -/
def RUN_CELL (f i g : ℕ → ℝ) : ℕ → ℝ → ℝ
  | 0, cell => cell
  | n + 1, cell => UPDATE_CELL (f n) (i n) (g n) (RUN_CELL f i g n cell)

/-- After `n` steps the difference between two memories has been multiplied by every forget
gate on the way. -/
theorem runCell_sub (f i g : ℕ → ℝ) (n : ℕ) (c₁ c₂ : ℝ) :
    RUN_CELL f i g n c₁ - RUN_CELL f i g n c₂ = (∏ t ∈ Finset.range n, f t) * (c₁ - c₂) := by
  induction n with
  | zero => simp [RUN_CELL]
  | succ n ih =>
    rw [RUN_CELL, RUN_CELL, UPDATE_CELL, UPDATE_CELL, Finset.prod_range_succ]
    linear_combination f n * ih

end SquigglyLine
