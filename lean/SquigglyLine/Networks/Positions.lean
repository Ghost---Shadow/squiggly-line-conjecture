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

Written in typical Mathlib style; waiting to be ported to `STYLE.md`.

Definitions: `GET_POSITION_OVERLAP`, `GET_PLANE_DOT`.

Theorems: `positionOverlap_eq_sum_cos`, `positionOverlap_shift`,
`positionOverlap_le_card`, `positionOverlap_self`, `planeDot_rotate_rotate`,
`planeDot_rotate_shift`, `planeDot_rotate_self`, `relativeBias_shift`,
`update_table_of_ne`.
-/
import SquigglyLine.Networks.Polarizer

namespace SquigglyLine

open Real

variable {ι : Type*} [Fintype ι]

/-- The overlap of the sinusoidal signals of two positions `p` and `q`, with one cosine and
one sine for each frequency `w k`.
Python: `sum(cos(w*p)*cos(w*q) + sin(w*p)*sin(w*q) for w in frequencies)`. -/
noncomputable def GET_POSITION_OVERLAP (w : ι → ℝ) (p q : ℝ) : ℝ :=
  ∑ k, (cos (w k * p) * cos (w k * q) + sin (w k * p) * sin (w k * q))

/-- **The overlap of two positions is a sum of cosines of their gap.** -/
theorem positionOverlap_eq_sum_cos (w : ι → ℝ) (p q : ℝ) :
    GET_POSITION_OVERLAP w p q = ∑ k, cos (w k * (p - q)) := by
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_sub, cos_sub]

/-- So it depends only on the gap: moving both positions along by `s` changes nothing. -/
theorem positionOverlap_shift (w : ι → ℝ) (p q s : ℝ) :
    GET_POSITION_OVERLAP w (p + s) (q + s) = GET_POSITION_OVERLAP w p q := by
  rw [positionOverlap_eq_sum_cos, positionOverlap_eq_sum_cos, add_sub_add_right_eq_sub]

/-- No two positions overlap more than a position does with itself. -/
theorem positionOverlap_le_card (w : ι → ℝ) (p q : ℝ) :
    GET_POSITION_OVERLAP w p q ≤ Fintype.card ι := by
  rw [positionOverlap_eq_sum_cos]
  calc ∑ k, cos (w k * (p - q)) ≤ ∑ _k : ι, (1 : ℝ) :=
        Finset.sum_le_sum fun k _ => cos_le_one _
    _ = Fintype.card ι := by simp

/-- A position's overlap with itself is the number of frequencies. -/
theorem positionOverlap_self (w : ι → ℝ) (p : ℝ) :
    GET_POSITION_OVERLAP w p p = Fintype.card ι := by
  rw [positionOverlap_eq_sum_cos]
  simp

/-- The dot product of two points of the plane.
Python: `a[0] * b[0] + a[1] * b[1]`. -/
def GET_PLANE_DOT (a b : PlanePoint) : ℝ :=
  a.1 * b.1 + a.2 * b.2

/-- **Rotary positions.** Turn the query by one angle and the key by another. Their dot
product is that of the query turned by the difference, with the key left alone. -/
theorem planeDot_rotate_rotate (α β : ℝ) (query key : PlanePoint) :
    GET_PLANE_DOT (ROTATE α query) (ROTATE β key)
      = GET_PLANE_DOT (ROTATE (α - β) query) key := by
  simp only [GET_PLANE_DOT, ROTATE, cos_sub, sin_sub]
  ring

/-- With angles `position * w`, the score depends on the two positions only through their
gap. -/
theorem planeDot_rotate_shift (w m n s : ℝ) (query key : PlanePoint) :
    GET_PLANE_DOT (ROTATE ((m + s) * w) query) (ROTATE ((n + s) * w) key)
      = GET_PLANE_DOT (ROTATE (m * w) query) (ROTATE (n * w) key) := by
  rw [planeDot_rotate_rotate, planeDot_rotate_rotate]
  congr 2
  ring

/-- Turning a vector does not change its length. -/
theorem planeDot_rotate_self (α : ℝ) (v : PlanePoint) :
    GET_PLANE_DOT (ROTATE α v) (ROTATE α v) = GET_PLANE_DOT v v := by
  simp only [GET_PLANE_DOT, ROTATE]
  nlinarith [sin_sq_add_cos_sq α]

/-- **A relative position bias** reads only the gap, so shifting the whole sequence leaves it
as it was. -/
theorem relativeBias_shift (bias : ℤ → ℝ) (i j s : ℤ) :
    bias ((j + s) - (i + s)) = bias (j - i) := by
  rw [add_sub_add_right_eq_sub]

/-- **A learned table ties no two positions together.** Changing the vector of one position
changes nothing at any other. -/
theorem update_table_of_ne {Position Vector : Type*} [DecidableEq Position]
    (table : Position → Vector) (changed : Position) (new_vector : Vector)
    {other : Position} (h : other ≠ changed) :
    Function.update table changed new_vector other = table other :=
  Function.update_of_ne h _ _

end SquigglyLine
