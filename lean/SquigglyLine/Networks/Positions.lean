/-
Position embeddings.

Four common ways to tell a transformer where a token is.

* **Sinusoidal, all frequencies together.** The overlap of the signals of two
  positions is a sum of cosines of the gap between them. It depends only on
  the gap and is largest at gap zero.
* **Rotary.** Turn the query and the key by angles set by their positions.
  The score then depends on the two positions only through their gap, and no
  vector changes length.
* **Relative position bias.** A number added to the score that depends only
  on the gap is unchanged when the whole sequence is shifted.
* **Learned table.** One free vector per position ties no two positions
  together: changing one entry changes nothing at any other position.

| Name                   | Meaning                                         |
|------------------------|-------------------------------------------------|
| `GET_POSITION_OVERLAP` | overlap of the sinusoidal signals of two places |
| `GET_PLANE_DOT`        | the dot product of two points of the plane      |

Theorems: `positionOverlap_eq_sum_cos`, `positionOverlap_shift`,
`positionOverlap_le_card`, `positionOverlap_self`, `planeDot_rotate_rotate`,
`planeDot_rotate_shift`, `planeDot_rotate_self`, `relativeBias_shift`,
`update_table_of_ne`.
-/
import SquigglyLine.Networks.Polarizer

namespace SquigglyLine

open Real

variable {Frequency : Type*} [Fintype Frequency]

/-- The overlap of the sinusoidal signals of two positions, with one cosine
and one sine for each frequency.
Python: `sum(cos(f*p)*cos(f*q) + sin(f*p)*sin(f*q) for f in frequencies)`
for positions `p` and `q`. -/
noncomputable def GET_POSITION_OVERLAP
    (frequencies : Frequency → ℝ)
    (position : ℝ)
    (other_position : ℝ) : ℝ :=
  ∑ k, (cos (frequencies k * position) * cos (frequencies k * other_position)
    + sin (frequencies k * position) * sin (frequencies k * other_position))

/-- **The overlap of two positions is a sum of cosines of their gap.** -/
theorem positionOverlap_eq_sum_cos
    (frequencies : Frequency → ℝ)
    (position : ℝ)
    (other_position : ℝ) :
    let overlap    := GET_POSITION_OVERLAP frequencies position other_position
    let gap        := position - other_position
    let cosine_sum := ∑ k, cos (frequencies k * gap)
    overlap = cosine_sum := by
  unfold_named_pieces
  refine Finset.sum_congr rfl fun k _ => ?_
  -- `cos a * cos b + sin a * sin b = cos (a - b)`.
  rw [mul_sub, cos_sub]

/-- So it depends only on the gap: moving both positions along by `shift`
changes nothing. -/
theorem positionOverlap_shift
    (frequencies : Frequency → ℝ)
    (position : ℝ)
    (other_position : ℝ)
    (shift : ℝ) :
    let shifted_overlap :=
      GET_POSITION_OVERLAP frequencies (position + shift)
        (other_position + shift)
    let overlap := GET_POSITION_OVERLAP frequencies position other_position
    shifted_overlap = overlap := by
  unfold_named_pieces
  have shifted_as_cosines :
      GET_POSITION_OVERLAP frequencies (position + shift)
          (other_position + shift)
        = ∑ k, cos (frequencies k
            * (position + shift - (other_position + shift))) :=
    positionOverlap_eq_sum_cos frequencies _ _
  have overlap_as_cosines :
      GET_POSITION_OVERLAP frequencies position other_position
        = ∑ k, cos (frequencies k * (position - other_position)) :=
    positionOverlap_eq_sum_cos frequencies _ _
  rw [shifted_as_cosines, overlap_as_cosines, add_sub_add_right_eq_sub]

/-- No two positions overlap more than a position does with itself. -/
theorem positionOverlap_le_card
    (frequencies : Frequency → ℝ)
    (position : ℝ)
    (other_position : ℝ) :
    let overlap :=
      GET_POSITION_OVERLAP frequencies position other_position
    let frequency_count : ℝ := Fintype.card Frequency  -- each cosine is at most one
    overlap ≤ frequency_count := by
  unfold_named_pieces
  have overlap_as_cosines :
      GET_POSITION_OVERLAP frequencies position other_position
        = ∑ k, cos (frequencies k * (position - other_position)) :=
    positionOverlap_eq_sum_cos frequencies _ _
  rw [overlap_as_cosines]
  calc ∑ k, cos (frequencies k * (position - other_position))
      ≤ ∑ _k : Frequency, (1 : ℝ) :=
        Finset.sum_le_sum fun k _ => cos_le_one _
    _ = Fintype.card Frequency := by simp

/-- A position's overlap with itself is the number of frequencies. -/
theorem positionOverlap_self
    (frequencies : Frequency → ℝ)
    (position : ℝ) :
    let overlap := GET_POSITION_OVERLAP frequencies position position
    let frequency_count : ℝ := Fintype.card Frequency  -- each cosine is exactly one at gap zero
    overlap = frequency_count := by
  unfold_named_pieces
  have overlap_as_cosines :
      GET_POSITION_OVERLAP frequencies position position
        = ∑ k, cos (frequencies k * (position - position)) :=
    positionOverlap_eq_sum_cos frequencies _ _
  rw [overlap_as_cosines]
  simp

/-- The dot product of two points of the plane.
Python: `point[0] * other_point[0] + point[1] * other_point[1]`. -/
def GET_PLANE_DOT
    (point : PlanePoint)
    (other_point : PlanePoint) : ℝ :=
  point.1 * other_point.1 + point.2 * other_point.2

/-- **Rotary positions.** Turn the query by one angle and the key by another.
Their dot product is that of the query turned by the difference, with the key
left alone. -/
theorem planeDot_rotate_rotate
    (query_angle : ℝ)
    (key_angle : ℝ)
    (query : PlanePoint)
    (key : PlanePoint) :
    let turned_query   := ROTATE query_angle query
    let turned_key     := ROTATE key_angle key
    let score          := GET_PLANE_DOT turned_query turned_key
    let angle_gap      := query_angle - key_angle
    let relative_query := ROTATE angle_gap query
    let relative_score := GET_PLANE_DOT relative_query key
    score = relative_score := by
  unfold_named_pieces
  simp only [GET_PLANE_DOT, ROTATE, cos_sub, sin_sub]
  ring

/-- With angles `position * frequency`, the score depends on the two positions
only through their gap. -/
theorem planeDot_rotate_shift
    (frequency : ℝ)
    (position : ℝ)
    (other_position : ℝ)
    (shift : ℝ)
    (query : PlanePoint)
    (key : PlanePoint) :
    let shifted_query := ROTATE ((position + shift) * frequency) query
    let shifted_key   := ROTATE ((other_position + shift) * frequency) key
    let shifted_score := GET_PLANE_DOT shifted_query shifted_key
    let plain_query   := ROTATE (position * frequency) query
    let plain_key     := ROTATE (other_position * frequency) key
    let plain_score   := GET_PLANE_DOT plain_query plain_key
    shifted_score = plain_score := by
  unfold_named_pieces
  have shifted_relative :
      GET_PLANE_DOT (ROTATE ((position + shift) * frequency) query)
          (ROTATE ((other_position + shift) * frequency) key)
        = GET_PLANE_DOT
            (ROTATE ((position + shift) * frequency
              - (other_position + shift) * frequency) query) key :=
    planeDot_rotate_rotate _ _ query key
  have plain_relative :
      GET_PLANE_DOT (ROTATE (position * frequency) query)
          (ROTATE (other_position * frequency) key)
        = GET_PLANE_DOT
            (ROTATE (position * frequency - other_position * frequency)
              query) key :=
    planeDot_rotate_rotate _ _ query key
  rw [shifted_relative, plain_relative]
  -- The shift cancels in the gap of the two angles.
  congr 2
  ring

/-- Turning a vector does not change its length. -/
theorem planeDot_rotate_self
    (angle : ℝ)
    (point : PlanePoint) :
    let turned_point          := ROTATE angle point
    let turned_squared_length := GET_PLANE_DOT turned_point turned_point
    let squared_length        := GET_PLANE_DOT point point
    turned_squared_length = squared_length := by
  unfold_named_pieces
  simp only [GET_PLANE_DOT, ROTATE]
  nlinarith [sin_sq_add_cos_sq angle]

/-- **A relative position bias** reads only the gap, so shifting the whole
sequence leaves it as it was. -/
theorem relativeBias_shift
    (bias : ℤ → ℝ)
    (query_position : ℤ)
    (key_position : ℤ)
    (shift : ℤ) :
    let shifted_bias := bias ((key_position + shift) - (query_position + shift))
    let plain_bias   := bias (key_position - query_position)
    shifted_bias = plain_bias := by
  unfold_named_pieces
  rw [add_sub_add_right_eq_sub]

/-- **A learned table ties no two positions together.** Changing the vector of
one position changes nothing at any other. -/
theorem update_table_of_ne
    {Position Vector : Type*}
    [DecidableEq Position]
    (table : Position → Vector)
    (changed : Position)
    (new_vector : Vector)
    {other : Position}
    (other_ne_changed : other ≠ changed) :
    let updated_table  := Function.update table changed new_vector
    let updated_vector := updated_table other
    let old_vector     := table other
    updated_vector = old_vector := by
  unfold_named_pieces
  exact Function.update_of_ne other_ne_changed _ _

end SquigglyLine
