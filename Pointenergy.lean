import Mathlib

open MeasureTheory

theorem single_point_has_energy (x₀ : ℝ) : Measure.dirac x₀ {x₀} = 1 := by
  simp

theorem zero_energy_is_zero (s : Set ℝ) : (0 : Measure ℝ) s = 0 := by
  simp

theorem anvil_principle (F : ℝ) (hF : 0 < F) (P : ℝ) :
    ∃ A : ℝ, 0 < A ∧ F / A > P := by
  by_cases hP : P ≤ 0
  · use 1
    constructor
    · linarith
    · calc F / 1 = F := by ring
        _ > P := by linarith
  · have hPpos : 0 < P := lt_of_not_ge hP
    use F / (P + 1)
    constructor
    · positivity
    · have hP1 : 0 < P + 1 := by linarith
      have : F / (F / (P + 1)) = P + 1 := by field_simp
      linarith