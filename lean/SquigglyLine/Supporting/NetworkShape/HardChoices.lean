/-
Hard choices: the straight-through trick, a cold softmax, and Hopfield recall.

* **Straight-through.** A hard step, such as rounding, has slope zero where
  it is not jumping, so no gradient comes back through it. The trick
  `(hard - soft).detach() + soft` has the value of the hard step and the
  slope of the gentle stand-in.
* **A cold softmax picks.** At temperature `temperature` the share of the top
  score is within `(choice_count - 1) * exp (-gap / temperature)` of one,
  where `gap` is its lead over the rest. This is the gentle stand-in of
  Gumbel-softmax, and it tends to the pick itself as the temperature falls.
* **Hopfield recall.** The update of a modern Hopfield network is an
  attention head over the stored patterns. For patterns and a query of
  length one it is the ideal denoiser of `Averaging.lean`.

Definitions: `APPLY_STRAIGHT_THROUGH`.

Theorems:
* `hasDerivAt_step_of_pos`        a hard step has slope zero away from its
                                  jump;
* `straightThrough_self`          forward, the trick is the hard step;
* `hasDerivAt_straightThrough`    backward, it has the slope of the stand-in;
* `one_sub_softmax_div_le`        a cold softmax gives the top score nearly
                                  all the share;
* `hopfield_eq_denoiser`          Hopfield recall is the ideal denoiser.
-/
import SquigglyLine.Supporting.NewInputs.Neighbours

namespace SquigglyLine

open Real

/-- **A hard step sends no gradient back.** Away from its jump, the step
function has slope zero. -/
theorem hasDerivAt_step_of_pos
    {point : ℝ}
    (point_pos : 0 < point) :
    let step : RealFunction := fun input => if 0 ≤ input then 1 else 0  -- jumps from 0 to 1 at the origin
    let slope : ℝ := 0
    HasDerivAt step slope point := by
  unfold_named_pieces
  -- Right of the jump the step is the constant 1.
  have step_is_one_nearby :
      (fun input : ℝ => if 0 ≤ input then (1 : ℝ) else 0)
        =ᶠ[nhds point] fun _ => 1 := by
    filter_upwards [eventually_gt_nhds point_pos] with input input_pos
    simp [input_pos.le]
  exact (hasDerivAt_const point (1 : ℝ)).congr_of_eventuallyEq
    step_is_one_nearby

/-- The straight-through trick at the point `anchor`: the hard value there,
with the gentle stand-in carrying the dependence on the input.
Python: `(hard(anchor) - soft(anchor)).detach() + soft(input)`. -/
def APPLY_STRAIGHT_THROUGH
    (hard soft : RealFunction)
    (anchor : ℝ) : RealFunction :=
  fun input => hard anchor - soft anchor + soft input

/-- **Forward, it is the hard step.** -/
theorem straightThrough_self
    (hard soft : RealFunction)
    (anchor : ℝ) :
    let forward    := APPLY_STRAIGHT_THROUGH hard soft anchor anchor
    let hard_value := hard anchor
    forward = hard_value := by
  unfold_named_pieces
  simp [APPLY_STRAIGHT_THROUGH]

/-- **Backward, it has the slope of the stand-in.** -/
theorem hasDerivAt_straightThrough
    (hard : RealFunction)
    {soft : RealFunction}
    {slope anchor : ℝ}
    (soft_has_slope : HasDerivAt soft slope anchor) :
    let through := APPLY_STRAIGHT_THROUGH hard soft anchor
    HasDerivAt through slope anchor := by
  unfold_named_pieces
  exact soft_has_slope.const_add (hard anchor - soft anchor)

variable {Choices : Type*} [Fintype Choices]

/-- **A cold softmax picks the top score.** If score `top` leads every other
by at least `gap`, then at temperature `temperature` its share is within
`(choice_count - 1) * exp (-gap / temperature)` of one. -/
theorem one_sub_softmax_div_le
    [DecidableEq Choices] [Nonempty Choices]
    {scores : Choices → ℝ}
    {top : Choices}
    {gap temperature : ℝ}
    (temperature_pos : 0 < temperature)
    (top_leads : ∀ j, j ≠ top → scores j + gap ≤ scores top) :
    let cold_scores := fun j => scores j / temperature
    let top_miss    := 1 - APPLY_SOFTMAX cold_scores top
    let bound       :=
      (Fintype.card Choices - 1) * exp (-gap / temperature)  -- each of the other choices has share at most exp (-gap / temperature)
    top_miss ≤ bound := by
  unfold_named_pieces
  have shares_sum_to_one :
      ∑ j, APPLY_SOFTMAX (fun j => scores j / temperature) j = 1 :=
    sum_softmax _
  -- What the top score misses is what the others hold.
  have miss_is_others_share :
      1 - APPLY_SOFTMAX (fun j => scores j / temperature) top
        = ∑ j ∈ Finset.univ.erase top,
            APPLY_SOFTMAX (fun j => scores j / temperature) j := by
    rw [← shares_sum_to_one,
      ← Finset.add_sum_erase _ _ (Finset.mem_univ top)]
    ring
  have top_exp_le_total :
      exp (scores top / temperature)
        ≤ ∑ k, exp (scores k / temperature) :=
    Finset.single_le_sum (f := fun k => exp (scores k / temperature))
      (fun k _ => (exp_pos _).le) (Finset.mem_univ top)
  have other_share_le :
      ∀ j ∈ Finset.univ.erase top,
        APPLY_SOFTMAX (fun j => scores j / temperature) j
          ≤ exp (-gap / temperature) := by
    intro j j_in_erase
    have j_ne_top : j ≠ top := Finset.ne_of_mem_erase j_in_erase
    calc APPLY_SOFTMAX (fun j => scores j / temperature) j
        = exp (scores j / temperature)
            / ∑ k, exp (scores k / temperature) := rfl
      _ ≤ exp (scores j / temperature) / exp (scores top / temperature) :=
          div_le_div_of_nonneg_left (exp_pos _).le (exp_pos _)
            top_exp_le_total
      _ = exp (scores j / temperature - scores top / temperature) := by
          rw [exp_sub]
      _ ≤ exp (-gap / temperature) := by
          refine exp_le_exp.mpr ?_
          rw [← sub_div]
          exact div_le_div_of_nonneg_right
            (by linarith [top_leads j j_ne_top]) temperature_pos.le
  have others_count :
      ((Finset.univ.erase top).card : ℝ) = Fintype.card Choices - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ top), Finset.card_univ,
      Nat.cast_sub Fintype.card_pos]
    simp
  calc 1 - APPLY_SOFTMAX (fun j => scores j / temperature) top
      = ∑ j ∈ Finset.univ.erase top,
          APPLY_SOFTMAX (fun j => scores j / temperature) j :=
        miss_is_others_share
    _ ≤ ∑ _j ∈ Finset.univ.erase top, exp (-gap / temperature) :=
        Finset.sum_le_sum other_share_le
    _ = (Fintype.card Choices - 1) * exp (-gap / temperature) := by
        rw [Finset.sum_const, nsmul_eq_mul, others_count]

variable {Space : Type*} [NormedAddCommGroup Space] [InnerProductSpace ℝ Space]
  [Nonempty Choices]

omit [Nonempty Choices] in
/-- **Hopfield recall is the ideal denoiser.** A modern Hopfield network
updates its state to an attention-weighted average of the stored patterns,
scored by overlap with the state. For patterns and a state of length one, that
is the ideal denoiser at noise level `√temperature`. -/
theorem hopfield_eq_denoiser
    {query : Space}
    {keys : Choices → Space}
    (query_is_unit : ‖query‖ = 1)
    (keys_are_unit : ∀ i, ‖keys i‖ = 1)
    {temperature : ℝ}
    (temperature_nonneg : 0 ≤ temperature) :
    let recalled :=
      ATTEND (fun i => inner ℝ query (keys i) / temperature) keys
    let denoised := DENOISE_IDEALLY (√temperature) keys query
    recalled = denoised := by
  unfold_named_pieces
  -- Cosine scores and squared-distance scores give the same shares.
  have same_shares :
      APPLY_SOFTMAX (fun i => inner ℝ query (keys i) / temperature)
        = APPLY_SOFTMAX
            fun i => -‖query - keys i‖ ^ 2 / (2 * temperature) :=
    softmax_cosine_eq_softmax_distance query_is_unit keys_are_unit
      temperature
  rw [DENOISE_IDEALLY, ATTEND, ATTEND, Real.sq_sqrt temperature_nonneg,
    same_shares]

end SquigglyLine
