/-
A gain per step: where it should be one, and where it should be below one.

`VanishingGradients.lean` shows that a gain `gain` per layer becomes
`gain ^ layer_count` after `layer_count` layers. Two well-known designs are
choices of that gain.

He initialisation, which sets the gain of a fold to one:
* `relu_sq_add_relu_neg_sq` : a fold keeps the squared size of the positive
  part and drops the rest: the two parts add up to the whole.
* `integral_relu_sq_of_symmetric` : so for a signal that is as often negative
  as positive, a fold keeps exactly half the mean squared size.
* `he_gain` : `input_count` inputs with weights of variance `2 / input_count`
  make up for the half.

The Bellman update of reinforcement learning, whose gain is below one:
* `lipschitzWith_bellman` : one sweep of value updates has slope at most the
  discount.
* `dist_iterate_bellman_le` : so after `sweep_count` sweeps any two guesses
  are within `discount ^ sweep_count` of their starting distance.

| Name                    | Meaning                                         |
|-------------------------|-------------------------------------------------|
| `max signal 0`          | a fold (ReLU): the signal if positive, else 0   |
| `RandomSignal Outcomes` | a signal that depends on a random outcome       |
| `NumberPerState States` | one number for each state: rewards, or values   |
| `MoveChances States`    | the chance of each move from state to state     |
| `APPLY_BELLMAN_SWEEP`   | one sweep of value updates                      |
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import SquigglyLine.Style

namespace SquigglyLine

open MeasureTheory NNReal

/-! ### Types -/

/-- A signal whose size depends on a random outcome.
Python: `Callable[[Outcome], float]`. -/
abbrev RandomSignal (Outcomes : Type*) := Outcomes → ℝ

/-- One number for each state: a table of rewards, or of guessed values.
Python: `dict[State, float]`. -/
abbrev NumberPerState (States : Type*) := States → ℝ

/-- The chance of each move: `move_chances state next_state` is the chance of
going from `state` to `next_state`.
Python: `dict[tuple[State, State], float]`. -/
abbrev MoveChances (States : Type*) := States → States → ℝ

/-! ### He initialisation -/

section He

/-- **A fold splits the squared size in two.** The part a ReLU keeps and the
part it would have kept of the mirror image add up to the whole. -/
theorem relu_sq_add_relu_neg_sq
    (signal : ℝ) :
    let kept_square   := max signal 0 ^ 2                          -- a fold lets the signal through if positive, else gives 0
    let mirror_square := max (-signal) 0 ^ 2                       -- the same fold on the mirror image keeps the negative part
    let whole_square  := signal ^ 2
    kept_square + mirror_square = whole_square := by               -- one of the two parts is always 0
  unfold_named_pieces
  rcases le_total 0 signal with signal_nonneg | signal_nonpos
  · rw [max_eq_left signal_nonneg,
      max_eq_right (neg_nonpos.mpr signal_nonneg)]
    ring
  · rw [max_eq_right signal_nonpos,
      max_eq_left (neg_nonneg.mpr signal_nonpos)]
    ring

variable {Outcomes : Type*} [MeasurableSpace Outcomes]
  (outcome_distribution : Measure Outcomes)

/-- **A fold keeps half.** If a signal is as often negative as positive, in
the sense that its mirror image has the same mean squared size after the
fold, then the fold keeps exactly half of the mean squared size. -/
theorem integral_relu_sq_of_symmetric
    {signal : RandomSignal Outcomes}
    (kept_square_has_mean :                                        -- `Integrable`: its average exists
      Integrable (fun outcome => max (signal outcome) 0 ^ 2)
        outcome_distribution)
    (mirror_square_has_mean :
      Integrable (fun outcome => max (-signal outcome) 0 ^ 2)
        outcome_distribution)
    (mirror_keeps_as_much :                                        -- as often negative as positive
      ∫ outcome, max (-signal outcome) 0 ^ 2 ∂outcome_distribution
        = ∫ outcome, max (signal outcome) 0 ^ 2 ∂outcome_distribution) :
    let mean_square_after_fold :=
      ∫ outcome, max (signal outcome) 0 ^ 2 ∂outcome_distribution  -- `∫ ... ∂`: the average over the random outcome
    let mean_square_before :=
      ∫ outcome, signal outcome ^ 2 ∂outcome_distribution
    mean_square_after_fold = mean_square_before / 2 := by          -- two equal parts that add up to the whole: each is half
  unfold_named_pieces
  -- The whole is the kept part plus the mirror's kept part, on average.
  have whole_is_sum_of_parts :
      ∫ outcome, signal outcome ^ 2 ∂outcome_distribution
        = ∫ outcome, max (signal outcome) 0 ^ 2 ∂outcome_distribution
          + ∫ outcome, max (-signal outcome) 0 ^ 2
              ∂outcome_distribution := by
    rw [← integral_add kept_square_has_mean mirror_square_has_mean]
    refine integral_congr_ae (ae_of_all _ fun outcome => ?_)
    exact (relu_sq_add_relu_neg_sq (signal outcome)).symm
  rw [whole_is_sum_of_parts, mirror_keeps_as_much]
  ring

/-- **The factor two of He initialisation.** A unit adds up `input_count`
inputs. With weights of variance `2 / input_count`, the half lost in the fold
is made up exactly, and the gain is one. -/
theorem he_gain
    {input_count : ℝ}
    (input_count_ne_zero : input_count ≠ 0) :
    let weight_variance : ℝ := 2 / input_count                     -- He's choice: the 2 is there to pay for the fold
    let kept_by_fold : ℝ    := 1 / 2                               -- a fold keeps half: `integral_relu_sq_of_symmetric`
    let gain := input_count * weight_variance * kept_by_fold       -- each input adds its variance, then the fold halves it
    gain = 1 := by
  unfold_named_pieces
  field_simp

end He

/-! ### The Bellman update -/

section Bellman

variable {States : Type*} [Fintype States]

/-- One sweep of value updates: the new value of a state is its reward, plus
the discounted average value of where it goes next.
Python: `{state: rewards[state] + discount * sum(move_chances[state, next] *
values[next] for next in states) for state in states}`. -/
def APPLY_BELLMAN_SWEEP
    (rewards : NumberPerState States)
    (move_chances : MoveChances States)
    (discount : ℝ)
    (values : NumberPerState States) : NumberPerState States :=
  fun state =>
    let average_next_value :=
      ∑ next_state, move_chances state next_state * values next_state  -- weighted by the chance of landing there
    rewards state + discount * average_next_value                  -- a reward later counts for less than a reward now

variable {move_chances : MoveChances States}

/-- **A sweep has slope at most the discount.** Two guesses at the values are
brought closer by the factor `discount`, measured by their largest
disagreement. -/
theorem lipschitzWith_bellman
    (chances_nonneg :
      ∀ state next_state, 0 ≤ move_chances state next_state)
    (chances_add_up_to_one :
      ∀ state, ∑ next_state, move_chances state next_state = 1)
    (discount : ℝ≥0)                                               -- `ℝ≥0`: a real number that is not negative
    (rewards : NumberPerState States) :
    let sweep := APPLY_BELLMAN_SWEEP rewards move_chances discount
    LipschitzWith discount sweep := by                             -- a gap between two guesses shrinks by the factor `discount`
  unfold_named_pieces
  refine LipschitzWith.of_dist_le_mul fun values other_values => ?_
  refine (dist_pi_le_iff (by positivity)).2 fun state => ?_
  -- The rewards cancel. What is left is the discount times an average of
  -- the disagreements.
  have difference_at_state :
      APPLY_BELLMAN_SWEEP rewards move_chances discount values state
        - APPLY_BELLMAN_SWEEP rewards move_chances discount
            other_values state
      = discount * ∑ next_state, move_chances state next_state
          * (values next_state - other_values next_state) := by
    simp only [APPLY_BELLMAN_SWEEP, mul_sub, Finset.sum_sub_distrib]
    ring
  rw [Real.dist_eq, difference_at_state, abs_mul,
    abs_of_nonneg discount.coe_nonneg]
  refine mul_le_mul_of_nonneg_left ?_ discount.coe_nonneg
  -- An average of disagreements is at most the largest disagreement.
  calc |∑ next_state, move_chances state next_state
          * (values next_state - other_values next_state)|
      ≤ ∑ next_state, |move_chances state next_state
          * (values next_state - other_values next_state)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ next_state, move_chances state next_state
          * dist values other_values :=
        Finset.sum_le_sum fun next_state _ => by
          have disagreement_at_most_largest :=
            dist_le_pi_dist values other_values next_state
          rw [Real.dist_eq] at disagreement_at_most_largest
          rw [abs_mul, abs_of_nonneg (chances_nonneg state next_state)]
          exact mul_le_mul_of_nonneg_left disagreement_at_most_largest
            (chances_nonneg state next_state)
    _ = dist values other_values := by
        rw [← Finset.sum_mul, chances_add_up_to_one, one_mul]

/-- **Repeated sweeps pull every guess to one answer.** After `sweep_count`
sweeps, two guesses differ by at most `discount ^ sweep_count` times what
they differed by at the start. -/
theorem dist_iterate_bellman_le
    (chances_nonneg :
      ∀ state next_state, 0 ≤ move_chances state next_state)
    (chances_add_up_to_one :
      ∀ state, ∑ next_state, move_chances state next_state = 1)
    (discount : ℝ≥0)
    (rewards : NumberPerState States)
    (sweep_count : ℕ)
    (values other_values : NumberPerState States) :
    let sweep := APPLY_BELLMAN_SWEEP rewards move_chances discount
    let gap_at_start := dist values other_values                   -- `dist` of two tables: their largest disagreement
    let gap_after_sweeps :=
      dist (sweep^[sweep_count] values)
        (sweep^[sweep_count] other_values)                         -- `sweep^[sweep_count]`: the sweep applied that many times
    let shrink_factor := (discount : ℝ) ^ sweep_count              -- one factor `discount` for each sweep
    gap_after_sweeps ≤ shrink_factor * gap_at_start := by
  unfold_named_pieces
  simpa using
    ((lipschitzWith_bellman chances_nonneg chances_add_up_to_one
      discount rewards).iterate sweep_count).dist_le_mul
        values other_values

end Bellman

end SquigglyLine
