/-
The GAN game: the best critic, and why the players spiral.

At one input, where real data lands with weight `real_weight` and made data
with weight `made_weight`, the critic's loss is a cross-entropy with the soft
label `real_weight / (real_weight + made_weight)`. So where both are present
the best critic predicts that share, and where made data is absent there is no
best score: the loss keeps asking for a larger one, which is a steeper critic.

For the payoff `x * y`, simultaneous gradient steps multiply the squared
distance from the resting point by `1 + learning_rate²`, so the two players
spiral outward.

Definitions: `GET_CRITIC_LOSS`, `TAKE_GAME_STEP`.

Theorems: `criticLoss_eq_logLoss`, `criticLoss_le_of_sigmoid_eq`,
`exists_best_critic`, `criticLoss_zero_le_of_eq`,
`strictAnti_criticLoss_of_no_fake`, `sq_add_sq_gameStep`,
`sq_add_sq_iterate_gameStep`, `sq_add_sq_lt_gameStep`.
-/
import SquigglyLine.Supporting.Training.CrossEntropy

namespace SquigglyLine

open Real

/-- The two players' numbers: the maker's number and the critic's number. -/
abbrev PlayerNumbers := ℝ × ℝ

/-- The critic's loss at one input, where real data lands with weight
`real_weight` and made data with weight `made_weight`, and the critic gives the
score `score`.
Python: `real_weight * GET_LOG_LOSS(1, score)
+ made_weight * GET_LOG_LOSS(0, score)`. -/
noncomputable def GET_CRITIC_LOSS
    (real_weight made_weight score : ℝ) : ℝ :=
  real_weight * GET_LOG_LOSS 1 score + made_weight * GET_LOG_LOSS 0 score

/-- **The critic's loss is a cross-entropy with a soft label.** The label is the
share of what lands at the input that is real. -/
theorem criticLoss_eq_logLoss
    {real_weight made_weight : ℝ}
    (total_weight_ne_zero : real_weight + made_weight ≠ 0)
    (score : ℝ) :
    let critic_loss := GET_CRITIC_LOSS real_weight made_weight score
    let real_share  := real_weight / (real_weight + made_weight)  -- the share of what lands here that is real
    let total_weight := real_weight + made_weight
    let soft_loss    := total_weight * GET_LOG_LOSS real_share score
    critic_loss = soft_loss := by
  unfold_named_pieces
  simp only [GET_CRITIC_LOSS, GET_LOG_LOSS]
  field_simp
  ring

/-- **The best critic predicts the real share.** Where real and made data are
both present, a score whose prediction is `real_weight / (real_weight +
made_weight)` has the least loss. -/
theorem criticLoss_le_of_sigmoid_eq
    {real_weight made_weight best_score : ℝ}
    (real_pos : 0 < real_weight)
    (made_pos : 0 < made_weight)
    (prediction_matches :
      sigmoid best_score = real_weight / (real_weight + made_weight))
    (score : ℝ) :
    let best_loss := GET_CRITIC_LOSS real_weight made_weight best_score
    let loss      := GET_CRITIC_LOSS real_weight made_weight score
    best_loss ≤ loss := by
  unfold_named_pieces
  have total_weight_pos : 0 < real_weight + made_weight :=
    add_pos real_pos made_pos
  have share_bound :
      GET_LOG_LOSS (real_weight / (real_weight + made_weight)) best_score
        ≤ GET_LOG_LOSS (real_weight / (real_weight + made_weight)) score :=
    logLoss_le_of_sigmoid_eq prediction_matches score
  have best_eq :
      GET_CRITIC_LOSS real_weight made_weight best_score
        = (real_weight + made_weight)
          * GET_LOG_LOSS (real_weight / (real_weight + made_weight))
              best_score :=
    criticLoss_eq_logLoss total_weight_pos.ne' best_score
  have loss_eq :
      GET_CRITIC_LOSS real_weight made_weight score
        = (real_weight + made_weight)
          * GET_LOG_LOSS (real_weight / (real_weight + made_weight)) score :=
    criticLoss_eq_logLoss total_weight_pos.ne' score
  rw [best_eq, loss_eq]
  exact mul_le_mul_of_nonneg_left share_bound total_weight_pos.le

/-- Where real and made data are both present, a best critic exists. -/
theorem exists_best_critic
    {real_weight made_weight : ℝ}
    (real_pos : 0 < real_weight)
    (made_pos : 0 < made_weight) :
    ∃ best_score : ℝ,
      let real_share := real_weight / (real_weight + made_weight)
      let predicts_share := sigmoid best_score = real_share
      let is_best := ∀ score : ℝ,
        let best_loss := GET_CRITIC_LOSS real_weight made_weight best_score
        let loss      := GET_CRITIC_LOSS real_weight made_weight score
        best_loss ≤ loss
      predicts_share ∧ is_best := by
  unfold_named_pieces
  have total_weight_pos : 0 < real_weight + made_weight :=
    add_pos real_pos made_pos
  have share_in_range :
      real_weight / (real_weight + made_weight) ∈ Set.range sigmoid := by
    rw [range_sigmoid]
    exact ⟨div_pos real_pos total_weight_pos,
      (div_lt_one total_weight_pos).mpr (by linarith)⟩
  obtain ⟨best_score, best_score_matches⟩ := share_in_range
  exact ⟨best_score, best_score_matches,
    criticLoss_le_of_sigmoid_eq real_pos made_pos best_score_matches⟩

/-- **When the maker has won, the critic cannot tell.** If real and made data
land with the same weight, the score zero (a prediction of one half) is
best. -/
theorem criticLoss_zero_le_of_eq
    {weight : ℝ}
    (weight_pos : 0 < weight)
    (score : ℝ) :
    let best_loss := GET_CRITIC_LOSS weight weight 0  -- score zero predicts one half
    let loss      := GET_CRITIC_LOSS weight weight score
    best_loss ≤ loss := by
  unfold_named_pieces
  -- Equal weights make the real share one half, which the score zero predicts.
  have half_share : weight / (weight + weight) = 1 / 2 := by
    rw [div_eq_iff (by positivity)]
    ring
  have zero_predicts_share : sigmoid 0 = weight / (weight + weight) := by
    rw [half_share, sigmoid_def]
    norm_num
  exact criticLoss_le_of_sigmoid_eq (best_score := 0) weight_pos weight_pos
    zero_predicts_share score

/-- **Where made data is absent, no score is best.** A larger score always has a
smaller loss, so the critic is asked to be steeper forever. -/
theorem strictAnti_criticLoss_of_no_fake
    {real_weight : ℝ}
    (real_pos : 0 < real_weight) :
    let loss_without_made := GET_CRITIC_LOSS real_weight 0
    StrictAnti loss_without_made := by
  unfold_named_pieces
  have log_loss_anti : StrictAnti (GET_LOG_LOSS 1) := strictAnti_logLoss_one
  intro low_score high_score low_lt_high
  simp only [GET_CRITIC_LOSS, zero_mul, add_zero]
  exact mul_lt_mul_of_pos_left (log_loss_anti low_lt_high) real_pos

/-- One simultaneous gradient step of the game with payoff `x * y`: the maker
lowers the payoff, the critic raises it.
Python: `(x - learning_rate * y, y + learning_rate * x)`. -/
def TAKE_GAME_STEP
    (learning_rate : ℝ)
    (state : PlayerNumbers) : PlayerNumbers :=
  (state.1 - learning_rate * state.2, state.2 + learning_rate * state.1)

/-- **One step outward.** A simultaneous step multiplies the squared distance
from the resting point by `1 + learning_rate²`. -/
theorem sq_add_sq_gameStep
    (learning_rate : ℝ)
    (state : PlayerNumbers) :
    let stepped         := TAKE_GAME_STEP learning_rate state
    let distance_after  := stepped.1 ^ 2 + stepped.2 ^ 2
    let distance_before := state.1 ^ 2 + state.2 ^ 2
    let growth          := 1 + learning_rate ^ 2  -- Pythagoras: each step is at right angles to the direction home
    distance_after = growth * distance_before := by
  unfold_named_pieces
  simp only [TAKE_GAME_STEP]
  ring

/-- **The players spiral outward.** After `step_count` simultaneous steps the
squared distance from the resting point has grown by `(1 + learning_rate²) ^
step_count`. -/
theorem sq_add_sq_iterate_gameStep
    (learning_rate : ℝ)
    (state : PlayerNumbers)
    (step_count : ℕ) :
    let stepped         := (TAKE_GAME_STEP learning_rate)^[step_count] state
    let distance_after  := stepped.1 ^ 2 + stepped.2 ^ 2
    let distance_before := state.1 ^ 2 + state.2 ^ 2
    let growth          := (1 + learning_rate ^ 2) ^ step_count  -- `1 + learning_rate²` per step
    distance_after = growth * distance_before := by
  unfold_named_pieces
  have one_step (position : PlayerNumbers) :
      (TAKE_GAME_STEP learning_rate position).1 ^ 2
          + (TAKE_GAME_STEP learning_rate position).2 ^ 2
        = (1 + learning_rate ^ 2) * (position.1 ^ 2 + position.2 ^ 2) :=
    sq_add_sq_gameStep learning_rate position
  induction step_count with
  | zero => simp
  | succ previous_count earlier_case =>
    rw [Function.iterate_succ_apply', one_step, earlier_case]
    ring

/-- Off the resting point, every step moves the players further from it. -/
theorem sq_add_sq_lt_gameStep
    {learning_rate : ℝ}
    (learning_rate_ne_zero : learning_rate ≠ 0)
    {state : PlayerNumbers}
    (away_from_rest : 0 < state.1 ^ 2 + state.2 ^ 2) :
    let stepped         := TAKE_GAME_STEP learning_rate state
    let distance_before := state.1 ^ 2 + state.2 ^ 2
    let distance_after  := stepped.1 ^ 2 + stepped.2 ^ 2
    distance_before < distance_after := by
  unfold_named_pieces
  have one_step :
      (TAKE_GAME_STEP learning_rate state).1 ^ 2
          + (TAKE_GAME_STEP learning_rate state).2 ^ 2
        = (1 + learning_rate ^ 2) * (state.1 ^ 2 + state.2 ^ 2) :=
    sq_add_sq_gameStep learning_rate state
  rw [one_step]
  have learning_rate_sq_pos : 0 < learning_rate ^ 2 := by positivity
  nlinarith

end SquigglyLine
