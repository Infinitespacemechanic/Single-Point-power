# pointenergy

> Only one will actually work. All it takes is one good shot to a single point, and you can break the toughest fields... the diamond anvil does it... but that one... it's a beast!

Formalization of concentrated energy vs zero energy in Lean 4 + Mathlib.

### The Idea

- **Single Point Energy (SPE)** = Dirac measure δ_{x₀}. Zero everywhere except one point, but integral = 1. Real, computable, does work. This is how computational chemistry single-point calculations work, and how a diamond anvil cell generates 300 GPa from a hand push.

- **Zero Energy** = Zero measure. Zero everywhere, integrates to 0. Does no work. Free-energy / vacuum extraction claims live here.

- **Anvil Principle**: `Pressure = Force / Area`. As `Area → 0`, `Pressure → ∞`. For any target pressure `P`, there exists a small enough area `A` such that `F/A > P`.

### Theorems

```lean
theorem single_point_has_energy (x₀ : ℝ) : Measure.dirac x₀ {x₀} = 1
theorem zero_energy_is_zero (s : Set ℝ) : (0 : Measure ℝ) s = 0
theorem anvil_principle (F : ℝ) (hF : 0 < F) (P : ℝ) : ∃ A, 0 < A ∧ F/A > P
theorem point_vs_volume (x₀ : ℝ) : dirac x₀ {x₀} = 1 ∧ volume {x₀} = 0
```

The last one is the beast: single point has zero volume (Lebesgue) but 1 unit of Dirac mass. That's why it breaks fields that volume-distributed force can't.

### Build

```bash
lake update
lake build
```

Tested on Lean 4.20.0 + mathlib master (2026-10-13 deploy).

### Structure

- `PointEnergy.lean` - main theory
- `MathlibDemo.lean` - shim for lean4web compatibility
- `lakefile.toml` - project config
- `lean-toolchain` - Lean version pin

### Masshole Corollary

> All it takes is one masshole to wreck the day!

Formal version: a single point defect (Dirac) can dominate a zero-mean field. One localized failure mode dominates distributed average.

License: MIT
