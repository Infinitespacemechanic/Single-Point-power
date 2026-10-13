import Mathlib

open MeasureTheory

/-!
# PointEnergy

One good shot to a single point breaks the toughest fields.
Diamond anvil principle formalized.

- `single_point_has_energy`: Dirac at x₀ carries 1 unit
- `zero_energy_is_zero`: zero measure carries 0 everywhere
- `anvil_principle`: F/A can exceed any P as A -> 0
-/

-- Single point carries energy
theorem single_point_has_energy (x₀ : ℝ) : Measure.dirac x₀ {x₀} = 1 := by
  simp

-- Zero spread does nothing
theorem zero_energy_is_zero (s : Set ℝ) : (0 : Measure ℝ) s = 0 := by
  simp

-- Diamond anvil: concentrated force beats any field
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

-- Extension: single point has zero Lebesgue volume but non-zero Dirac mass
-- This is why the beast works
theorem point_vs_volume (x₀ : ℝ) :
    Measure.dirac x₀ {x₀} = 1 ∧ volume ({x₀} : Set ℝ) = 0 := by
  constructor
  · simp
  · simp
