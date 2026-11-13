/-
The GAN game: the best critic, and why the players spiral.

At one input, where real data lands with weight `p` and made data with
weight `q`, the critic's loss is a cross-entropy with the soft label
`p / (p + q)`. So where both are present the best critic predicts that
share, and where made data is absent there is no best score: the loss keeps
asking for a larger one, which is a steeper critic.

For the payoff `x * y`, simultaneous gradient steps multiply the squared
distance from the resting point by `1 + η²`, so the two players spiral
outward.

Definitions: `GET_CRITIC_LOSS`, `TAKE_GAME_STEP`.

Theorems: `criticLoss_eq_logLoss`, `criticLoss_le_of_sigmoid_eq`,
`exists_best_critic`, `criticLoss_zero_le_of_eq`,
`strictAnti_criticLoss_of_no_fake`, `sq_add_sq_gameStep`,
`sq_add_sq_iterate_gameStep`, `sq_add_sq_lt_gameStep`.
-/
import SquigglyLine.Supporting.Training.CrossEntropy

namespace SquigglyLine

open Real

/-- The critic's loss at one input, where real data lands with weight `p` and made data with
weight `q`, and the critic gives the score `z`.
Python: `p * GET_LOG_LOSS(1, z) + q * GET_LOG_LOSS(0, z)`. -/
noncomputable def GET_CRITIC_LOSS (p q z : ℝ) : ℝ :=
  p * GET_LOG_LOSS 1 z + q * GET_LOG_LOSS 0 z

/-- **The critic's loss is a cross-entropy with a soft label.** The label is the share of
what lands at the input that is real. -/
theorem criticLoss_eq_logLoss {p q : ℝ} (h : p + q ≠ 0) (z : ℝ) :
    GET_CRITIC_LOSS p q z = (p + q) * GET_LOG_LOSS (p / (p + q)) z := by
  simp only [GET_CRITIC_LOSS, GET_LOG_LOSS]
  field_simp
  ring

/-- **The best critic predicts the real share.** Where real and made data are both present,
a score whose prediction is `p / (p + q)` has the least loss. -/
theorem criticLoss_le_of_sigmoid_eq {p q z₀ : ℝ} (hp : 0 < p) (hq : 0 < q)
    (hz : sigmoid z₀ = p / (p + q)) (z : ℝ) :
    GET_CRITIC_LOSS p q z₀ ≤ GET_CRITIC_LOSS p q z := by
  have hpq : 0 < p + q := add_pos hp hq
  have h : GET_LOG_LOSS (p / (p + q)) z₀ ≤ GET_LOG_LOSS (p / (p + q)) z :=
    logLoss_le_of_sigmoid_eq hz z
  rw [criticLoss_eq_logLoss hpq.ne', criticLoss_eq_logLoss hpq.ne']
  exact mul_le_mul_of_nonneg_left h hpq.le

/-- Where real and made data are both present, a best critic exists. -/
theorem exists_best_critic {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    ∃ z₀ : ℝ, sigmoid z₀ = p / (p + q) ∧
      ∀ z : ℝ, GET_CRITIC_LOSS p q z₀ ≤ GET_CRITIC_LOSS p q z := by
  have hpq : 0 < p + q := add_pos hp hq
  have hmem : p / (p + q) ∈ Set.range sigmoid := by
    rw [range_sigmoid]
    exact ⟨div_pos hp hpq, (div_lt_one hpq).mpr (by linarith)⟩
  obtain ⟨z₀, hz₀⟩ := hmem
  exact ⟨z₀, hz₀, criticLoss_le_of_sigmoid_eq hp hq hz₀⟩

/-- **When the maker has won, the critic cannot tell.** If real and made data land with the
same weight, the score zero (a prediction of one half) is best. -/
theorem criticLoss_zero_le_of_eq {p : ℝ} (hp : 0 < p) (z : ℝ) :
    GET_CRITIC_LOSS p p 0 ≤ GET_CRITIC_LOSS p p z := by
  refine criticLoss_le_of_sigmoid_eq hp hp ?_ z
  have hhalf : p / (p + p) = 1 / 2 := by
    rw [div_eq_iff (by positivity)]
    ring
  rw [hhalf, sigmoid_def]
  norm_num

/-- **Where made data is absent, no score is best.** A larger score always has a smaller
loss, so the critic is asked to be steeper forever. -/
theorem strictAnti_criticLoss_of_no_fake {p : ℝ} (hp : 0 < p) :
    StrictAnti (GET_CRITIC_LOSS p 0) := by
  have h : StrictAnti (GET_LOG_LOSS 1) := strictAnti_logLoss_one
  intro a b hab
  simp only [GET_CRITIC_LOSS, zero_mul, add_zero]
  exact mul_lt_mul_of_pos_left (h hab) hp

/-- One simultaneous gradient step of the game with payoff `x * y`: the maker lowers the
payoff, the critic raises it.
Python: `(x - η * y, y + η * x)`. -/
def TAKE_GAME_STEP (η : ℝ) (s : ℝ × ℝ) : ℝ × ℝ :=
  (s.1 - η * s.2, s.2 + η * s.1)

/-- **One step outward.** A simultaneous step multiplies the squared distance from the
resting point by `1 + η²`. -/
theorem sq_add_sq_gameStep (η : ℝ) (s : ℝ × ℝ) :
    (TAKE_GAME_STEP η s).1 ^ 2 + (TAKE_GAME_STEP η s).2 ^ 2
      = (1 + η ^ 2) * (s.1 ^ 2 + s.2 ^ 2) := by
  simp only [TAKE_GAME_STEP]
  ring

/-- **The players spiral outward.** After `n` simultaneous steps the squared distance from
the resting point has grown by `(1 + η²) ^ n`. -/
theorem sq_add_sq_iterate_gameStep (η : ℝ) (s : ℝ × ℝ) (n : ℕ) :
    ((TAKE_GAME_STEP η)^[n] s).1 ^ 2 + ((TAKE_GAME_STEP η)^[n] s).2 ^ 2
      = (1 + η ^ 2) ^ n * (s.1 ^ 2 + s.2 ^ 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', sq_add_sq_gameStep, ih]
    ring

/-- Off the resting point, every step moves the players further from it. -/
theorem sq_add_sq_lt_gameStep {η : ℝ} (hη : η ≠ 0) {s : ℝ × ℝ}
    (hs : 0 < s.1 ^ 2 + s.2 ^ 2) :
    s.1 ^ 2 + s.2 ^ 2 < (TAKE_GAME_STEP η s).1 ^ 2 + (TAKE_GAME_STEP η s).2 ^ 2 := by
  rw [sq_add_sq_gameStep]
  have hη2 : 0 < η ^ 2 := by positivity
  nlinarith

end SquigglyLine
