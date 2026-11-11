/-
Double descent, as the travel peak.

Two inequalities connect the test-error peak of double descent to the
distance from the start to the nearest fit.

* `exists_fit_near_start`: there is a fit whose output on any feature vector
  differs from the output at the start by at most the size of that vector
  times the travel. A fit that is near the start is tame everywhere.
* `travel_le_of_le_kernel`: if the kernel is at least `c` in every direction,
  the travel is at most the size of the residual divided by `√c`. The travel
  can be large only where the kernel has a weak direction, which is what
  happens when the model has barely enough parameters to fit.

That the test error does peak there is measured (`scripts/double_descent.py`),
not proved.
-/
import SquigglyLine.Kernel

namespace SquigglyLine

open ContinuousLinearMap

variable {Θ Y : Type*}
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

omit [CompleteSpace Θ] in
/-- The output on a feature vector `φ` moves by at most `‖φ‖` times the distance moved in
parameter space. -/
theorem abs_inner_sub_le (φ θ θ₀ : Θ) :
    |inner ℝ φ θ - inner ℝ φ θ₀| ≤ ‖φ‖ * ‖θ - θ₀‖ := by
  rw [← inner_sub_right]
  exact abs_real_inner_le_norm _ _

/-- **A fit near the start is tame everywhere.** There is a fit whose output on every
feature vector is within `‖φ‖` times the travel of the output at the start. -/
theorem exists_fit_near_start (A : Θ →L[ℝ] Y) (Kinv : Y → Y)
    (hinv : ∀ v, A (adjoint A (Kinv v)) = v) (y : Y) (θ₀ : Θ) :
    ∃ θ, A θ = y ∧
      ∀ φ : Θ, |inner ℝ φ θ - inner ℝ φ θ₀| ≤ ‖φ‖ * travel (A : Θ →ₗ[ℝ] Y) y θ₀ := by
  refine ⟨θ₀ + adjoint A (Kinv (residual (A : Θ →ₗ[ℝ] Y) y θ₀)), ?_, fun φ => ?_⟩
  · rw [map_add, hinv]
    simp [residual]
  · rw [travel_eq_norm_of_kernelInverse A Kinv hinv]
    calc |inner ℝ φ (θ₀ + adjoint A (Kinv (residual (A : Θ →ₗ[ℝ] Y) y θ₀))) - inner ℝ φ θ₀|
        ≤ ‖φ‖ * ‖θ₀ + adjoint A (Kinv (residual (A : Θ →ₗ[ℝ] Y) y θ₀)) - θ₀‖ :=
          abs_inner_sub_le _ _ _
      _ = ‖φ‖ * ‖adjoint A (Kinv (residual (A : Θ →ₗ[ℝ] Y) y θ₀))‖ := by
          rw [add_sub_cancel_left]

/-- **The travel is large only where the kernel is weak.** If the kernel is at least `c` in
every direction, the travel is at most the size of the residual divided by `√c`. -/
theorem travel_le_of_le_kernel (A : Θ →L[ℝ] Y) (Kinv : Y → Y)
    (hinv : ∀ v, A (adjoint A (Kinv v)) = v) {c : ℝ} (hc : 0 < c)
    (hK : ∀ v, c * ‖v‖ ^ 2 ≤ inner ℝ (A (adjoint A v)) v) (y : Y) (θ₀ : Θ) :
    travel (A : Θ →ₗ[ℝ] Y) y θ₀ ≤ ‖residual (A : Θ →ₗ[ℝ] Y) y θ₀‖ / √c := by
  obtain ⟨r, hr⟩ : ∃ r, r = residual (A : Θ →ₗ[ℝ] Y) y θ₀ := ⟨_, rfl⟩
  rw [travel_eq_norm_of_kernelInverse A Kinv hinv, ← hr]
  have hsq_eq := norm_adjoint_kernelInverse_sq A Kinv hinv r
  have hinvr := hinv r
  obtain ⟨u, hu⟩ : ∃ u, u = Kinv r := ⟨_, rfl⟩
  rw [← hu] at hsq_eq hinvr ⊢
  have h1 : c * ‖u‖ ^ 2 ≤ ‖r‖ * ‖u‖ :=
    calc c * ‖u‖ ^ 2 ≤ inner ℝ (A (adjoint A u)) u := hK u
      _ = inner ℝ r u := by rw [hinvr]
      _ ≤ ‖r‖ * ‖u‖ := real_inner_le_norm _ _
  have h2 : c * ‖u‖ ≤ ‖r‖ := by
    rcases eq_or_lt_of_le (norm_nonneg u) with h0 | hpos
    · rw [← h0, mul_zero]
      exact norm_nonneg _
    · have h3 : ‖u‖ * (c * ‖u‖) ≤ ‖u‖ * ‖r‖ := by nlinarith [h1]
      exact le_of_mul_le_mul_left h3 hpos
  have hsq : ‖adjoint A u‖ ^ 2 ≤ ‖r‖ ^ 2 / c := by
    rw [hsq_eq, le_div_iff₀ hc]
    calc inner ℝ u r * c ≤ ‖u‖ * ‖r‖ * c :=
          mul_le_mul_of_nonneg_right (real_inner_le_norm _ _) hc.le
      _ = c * ‖u‖ * ‖r‖ := by ring
      _ ≤ ‖r‖ * ‖r‖ := mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
      _ = ‖r‖ ^ 2 := by ring
  calc ‖adjoint A u‖
      = √(‖adjoint A u‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ √(‖r‖ ^ 2 / c) := Real.sqrt_le_sqrt hsq
    _ = ‖r‖ / √c := by rw [Real.sqrt_div (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

/-! ### The peak, exactly: one direction of the labels

Follow one direction `r` of the labels that the kernel stretches by `lam`.
`lam = 0`: out of reach. `lam` small: reachable at a huge price. `lam` large: cheap. -/

/-- The kernel is symmetric. -/
theorem kernel_inner_comm (A : Θ →L[ℝ] Y) (u v : Y) :
    inner ℝ (A (adjoint A u)) v = inner ℝ u (A (adjoint A v)) :=
  (adjoint_inner_right A (adjoint A u) v).symm.trans (adjoint_inner_left A (adjoint A v) u)

/-- **Strength zero: out of reach.** If the kernel sends a direction to zero, no change of
the parameters produces it. The model cannot fit that part of the labels. -/
theorem not_exists_fit_of_kernel_eq_zero (A : Θ →L[ℝ] Y) {r : Y} (hr : r ≠ 0)
    (hK : A (adjoint A r) = 0) : ¬ ∃ δ, A δ = r := by
  rintro ⟨δ, hδ⟩
  have h0 : adjoint A r = 0 := by
    have hsq : ‖adjoint A r‖ ^ 2 = 0 := by
      rw [← real_inner_self_eq_norm_sq, adjoint_inner_left, hK, inner_zero_right]
    simpa using hsq
  have hsq : ‖r‖ ^ 2 = 0 := by
    rw [← real_inner_self_eq_norm_sq]
    nth_rewrite 2 [← hδ]
    rw [← adjoint_inner_left, h0, inner_zero_left]
  exact hr (by simpa using hsq)

/-- **Strength `lam`: the exact price.** If the residual lies along a direction that the
kernel stretches by `lam > 0`, the travel is exactly the size of the residual divided by
`√lam`. -/
theorem travel_eq_of_eigen (A : Θ →L[ℝ] Y) (Kinv : Y → Y)
    (hinv : ∀ v, A (adjoint A (Kinv v)) = v) {lam : ℝ} (hlam : 0 < lam) (y : Y) (θ₀ : Θ)
    (heig : A (adjoint A (residual (A : Θ →ₗ[ℝ] Y) y θ₀))
      = lam • residual (A : Θ →ₗ[ℝ] Y) y θ₀) :
    travel (A : Θ →ₗ[ℝ] Y) y θ₀ = ‖residual (A : Θ →ₗ[ℝ] Y) y θ₀‖ / √lam := by
  obtain ⟨r, hr⟩ : ∃ r, r = residual (A : Θ →ₗ[ℝ] Y) y θ₀ := ⟨_, rfl⟩
  rw [travel_eq_norm_of_kernelInverse A Kinv hinv, ← hr]
  rw [← hr] at heig
  have key : lam * inner ℝ (Kinv r) r = ‖r‖ ^ 2 := by
    rw [← real_inner_smul_right, ← heig, ← kernel_inner_comm, hinv r,
      real_inner_self_eq_norm_sq]
  have hsq : ‖adjoint A (Kinv r)‖ ^ 2 = ‖r‖ ^ 2 / lam := by
    rw [norm_adjoint_kernelInverse_sq A Kinv hinv r, eq_div_iff hlam.ne', mul_comm]
    exact key
  calc ‖adjoint A (Kinv r)‖
      = √(‖adjoint A (Kinv r)‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ = √(‖r‖ ^ 2 / lam) := by rw [hsq]
    _ = ‖r‖ / √lam := by rw [Real.sqrt_div (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

/-- **The peak.** The weaker the direction, the further the fit: if the kernel stretches the
residual's direction by at most `ε²`, the travel is at least the size of the residual divided
by `ε`. As `ε` goes to zero this grows without bound. -/
theorem le_travel_of_eigen_le (A : Θ →L[ℝ] Y) (Kinv : Y → Y)
    (hinv : ∀ v, A (adjoint A (Kinv v)) = v) {lam ε : ℝ} (hlam : 0 < lam) (hε : 0 < ε)
    (hle : lam ≤ ε ^ 2) (y : Y) (θ₀ : Θ)
    (heig : A (adjoint A (residual (A : Θ →ₗ[ℝ] Y) y θ₀))
      = lam • residual (A : Θ →ₗ[ℝ] Y) y θ₀) :
    ‖residual (A : Θ →ₗ[ℝ] Y) y θ₀‖ / ε ≤ travel (A : Θ →ₗ[ℝ] Y) y θ₀ := by
  rw [travel_eq_of_eigen A Kinv hinv hlam y θ₀ heig]
  refine div_le_div_of_nonneg_left (norm_nonneg _) (Real.sqrt_pos.mpr hlam) ?_
  calc √lam ≤ √(ε ^ 2) := Real.sqrt_le_sqrt hle
    _ = ε := Real.sqrt_sq hε.le

/-! ### The smallest example: one training point -/

/-- With one training point and feature vector `a`, the kernel is the squared length of
`a`. Adding features can only make it larger. -/
theorem tightFeatures_innerSL (a : Θ) : TightFeatures (innerSL ℝ a) (‖a‖ ^ 2) := by
  intro t
  rw [adjoint_innerSL_apply]
  simp [mul_comm]

/-- **One training point.** The distance to the nearest fit is the error divided by the
length of the feature vector. A short feature vector means a distant fit. -/
theorem travel_one_point {a : Θ} (ha : a ≠ 0) (y : ℝ) (θ₀ : Θ) :
    travel (innerSL ℝ a : Θ →ₗ[ℝ] ℝ) y θ₀ = |y - inner ℝ a θ₀| / ‖a‖ := by
  rw [(tightFeatures_innerSL a).travel_eq (pow_pos (norm_pos_iff.mpr ha) 2) y θ₀,
    Real.sqrt_sq (norm_nonneg a)]
  simp [residual, Real.norm_eq_abs]

end SquigglyLine
