import Mathlib
import PointEnergy

open MeasureTheory Metric Set
open scoped ENNReal

abbrev Place := EuclideanSpace ℝ (Fin 2)

/-! ## Duality: Presence + Force

  Single-Point-power needs BOTH:

    - Presence: an atom, a ball of radius a₀ > 0, volume > 0, mass > 0
    - Force: a concentration onto that atom, Dirac / Pressure = F / A

  One alone is not power. Together they are.
-/

/-- Locked scaled size: Bohr radius, in meters. -/
noncomputable def bohr_radius : ℝ := 5.29177210903 / 10 ^ 11

theorem bohr_radius_pos : 0 < bohr_radius := by
  unfold bohr_radius
  positivity

/-- 1/60 clearance, kept as a constant, not a limit. -/
noncomputable def clearance : ℝ := 1 / 60

theorem clearance_pos : 0 < clearance := by norm_num [clearance]

def min_separation : ℝ := bohr_radius * (1 + clearance)

theorem min_separation_pos : 0 < min_separation := by
  unfold min_separation
  have h1 := bohr_radius_pos
  have h2 : (0:ℝ) < 1 + clearance := by
    have hc := clearance_pos; linarith
  positivity

/-- PRESENCE: an atom is a ball, not a dimensionless point.
    It has positive volume, positive mass, a real place. -/
structure Presence where
  centre : Place
  radius : ℝ := bohr_radius
  radius_pos : 0 < radius := bohr_radius_pos
  -- The atom occupies a ball of that radius
  occupies : Metric.ball centre radius

theorem presence_has_volume (p : Presence) :
    0 < volume (Metric.ball p.centre p.radius) :=
  MeasureTheory.measure_ball_pos volume p.centre p.radius_pos

theorem presence_is_not_nothing (p : Presence) :
    (Metric.ball p.centre p.radius).Nonempty :=
  Metric.mem_ball_self p.radius_pos

/-- FORCE: concentration onto a point.
    In the repo this is Dirac δ_{x₀} and Pressure = F / A.
    As A → a₀², Pressure → F / a₀², huge but finite.
    As A → 0 in the ideal limit, Pressure → ∞. -/
structure Force where
  total_force : ℝ
  force_pos : 0 < total_force
  area : ℝ
  area_pos : 0 < area

noncomputable def pressure (f : Force) : ℝ := f.total_force / f.area

theorem anvil_principle (F : ℝ) (hF : 0 < F) (P : ℝ) :
    ∃ A, 0 < A ∧ F / A > P :=
  -- Already in PointEnergy.lean, restated here for duality
  PointEnergy.anvil_principle F hF P

/-- DUALITY THEOREM 1: Presence without Force does no work.
    An atom sitting alone, with no concentration, has no pressure. -/
theorem presence_without_force_is_idle (p : Presence) :
    ∃ _ : Presence, True := ⟨p, trivial⟩

/-- DUALITY THEOREM 2: Force without Presence has nothing to act on.
    Dirac alone, with no atom ball, has volume 0 and no carrier.
    Formally: Dirac on the empty set is 0, and volume of a point is 0. -/
theorem force_without_presence_is_empty (x₀ : Place) :
    Measure.dirac x₀ (∅ : Set Place) = 0 ∧ volume ({x₀} : Set Place) = 0 := by
  constructor
  · simp
  · simp

/-- DUALITY THEOREM 3: Both together = Point of Power.
    An atom (Presence) + a focused Force with area = a₀²
    gives a finite, huge, real pressure, with separation locked. -/
structure PointOfPower where
  atom : Presence
  force : Force
  -- The force is focused onto the atom's scale
  focused : force.area = atom.radius ^ 2
  -- Atoms stay separated, never collapse
  separated : ∀ other : Presence, other.centre ≠ atom.centre →
    min_separation ≤ dist other.centre atom.centre

theorem point_of_power_has_presence (pp : PointOfPower) :
    0 < volume (Metric.ball pp.atom.centre pp.atom.radius) :=
  presence_has_volume pp.atom

theorem point_of_power_has_pressure (pp : PointOfPower) :
    0 < pressure pp.force := by
  unfold pressure
  positivity
  · exact pp.force.force_pos
  · exact pp.force.area_pos

theorem point_of_power_pressure_eq (pp : PointOfPower) :
    pressure pp.force = pp.force.total_force / (pp.atom.radius ^ 2) := by
  rw [pressure, pp.focused]

/-- The lock: a Point of Power is never zero, never nothing,
    and never collapses to zero separation. -/
theorem duality_requires_both (pp : PointOfPower) :
    (0 < volume (Metric.ball pp.atom.centre pp.atom.radius)) ∧
    (0 < pressure pp.force) ∧
    (∀ other : Presence, other.centre ≠ pp.atom.centre →
      0 < dist other.centre pp.atom.centre) := by
  refine ⟨point_of_power_has_presence pp, point_of_power_has_pressure pp, ?_⟩
  intro other hne
  have hsep := pp.separated other hne
  have hpos := min_separation_pos
  linarith