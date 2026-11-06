# pointenergy

> Only one will actually work. All it takes is one good shot to a single point, and you can break the toughest fields... the diamond anvil does it... but that one... it's a beast!

Formalization of concentrated energy vs zero energy in Lean 4 + Mathlib.

### The Idea

- **Single Point Energy (SPE)** = Dirac measure δ_{x₀}. Zero everywhere except one point, but integral = 1. Real, computable, does work. This is how computational chemistry single-point calculations work, and how a diamond anvil cell generates 300 GPa from a hand push.

- **Zero Energy** = Zero measure. Zero everywhere, integrates to 0. Does no work. Free-energy / vacuum extraction claims live here.

- **Anvil Principle**: `Pressure = Force / Area`. As `Area → 0`, `Pressure → ∞`. For any target pressure `P`, there exists a small enough area `A` such that `F/A > P`.

### Theorems
