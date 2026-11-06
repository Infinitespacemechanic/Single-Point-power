import Mathlib

/-! ## Zero Rules
  Zero is not a thing. Zero is "not yet."
  Zero in multiplication = zero copies, not destroy.
  Zero in addition = do nothing.
  Zero as a limit ≠ zero as a state.
-/

/-- RULE 1: Zero is "not a place", not a place.
    A real thing has > 0. Once placed, it's not zero. -/
theorem zero_is_not_a_place (a : ℝ) (h : 0 < a) : a ≠ 0 :=
  ne_of_gt h

/-- RULE 2: Zero in addition does nothing. -/
theorem zero_add_does_nothing (a : ℝ) : a + 0 = a := add_zero a
theorem zero_add_left_does_nothing (a : ℝ) : 0 + a = a := zero_add a

/-- RULE 3: Zero in multiplication = zero copies, NOT destroy.
    `owned` = what you already have.
    `make_new` = what the operation makes new.
    Making 0 groups makes 0 new, but `owned` is untouched. -/
def make_new (groups : ℕ) (size : ℕ) : ℕ := groups * size

theorem make_zero_groups_makes_zero (size : ℕ) :
    make_new 0 size = 0 := by
  simp [make_new]

theorem donut_rule (owned : ℕ) (size : ℕ) :
    -- You own `owned` donuts. You make 0 groups of `size`.
    -- You end with `owned` + 0 new = `owned`. The old ones are still there.
    owned + make_new 0 size = owned := by
  simp [make_new]

-- Concrete: 4 donuts, 0 new groups, still 4 donuts
example : 4 + make_new 0 4 = 4 := donut_rule 4 4
example : make_new 0 4 = 0 := make_zero_groups_makes_zero 4

/-- RULE 4: 4 × 0 = 0 does NOT mean 4 = 0.
    The operation result is 0, the input is still 4. -/
theorem mul_zero_does_not_erase (a : ℝ) (h : a ≠ 0) : a * 0 = 0 ∧ a ≠ 0 :=
  ⟨mul_zero a, h⟩

example : (4 : ℝ) * 0 = 0 ∧ (4 : ℝ) ≠ 0 :=
  mul_zero_does_not_erase 4 (by norm_num)

/-- RULE 5: Zero can never be a denominator.
    Pressure = F / A needs A > 0. -/
theorem pressure_needs_positive_area (F A : ℝ) (hA : 0 < A) :
    A ≠ 0 := ne_of_gt hA

theorem anvil_area_never_zero (F : ℝ) (hF : 0 < F) (P : ℝ) :
    ∃ A, 0 < A ∧ F / A > P := by
  -- Choose A = F / (|P| + F + 1), then F / A = |P| + F + 1 > P
  use F / (|P| + F + 1)
  constructor
  · positivity
  · have hden : (0:ℝ) < |P| + F + 1 := by
      have h1 := abs_nonneg P
      linarith
    have hEq : F / (F / (|P| + F + 1)) = |P| + F + 1 := by
      field_simp
    rw [hEq]
    -- FIX: need BOTH sides of |P|: P ≤ |P| AND -P ≤ |P|
    have h_le : P ≤ |P| := le_abs_self P
    have h_pos : (0:ℝ) < F + 1 := by linarith
    linarith

/-- RULE 6: Zero as a limit ≠ zero as a state.
    You can approach 0, but a real atom never IS 0. -/
theorem limit_is_not_state (a₀ : ℝ) (h : 0 < a₀) :
    a₀ ≠ 0 ∧ a₀ * (1 + 1 / 60) ≠ 0 := by
  constructor
  · exact ne_of_gt h
  · have h2 : (0:ℝ) < 1 + 1 / 60 := by norm_num
    exact ne_of_gt (mul_pos h h2)

/-- RULE 7: Zero does not erase Presence.
    0 force means 0 new power, but Presence is still there. -/
theorem zero_force_does_not_erase_presence
    (presence_volume : ℝ) (hvol : 0 < presence_volume) :
    presence_volume ≠ 0 ∧ presence_volume + 0 = presence_volume :=
  ⟨ne_of_gt hvol, add_zero presence_volume⟩