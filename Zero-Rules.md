### Zero Rules

Zero is not a thing. Zero is "not yet."

People flip out when zeros don't work because we use the same word "zero" for three different things.

- **Zero in addition does nothing.** `a + 0 = a`. Zero added changes nothing.

- **Zero in multiplication = zero copies, NOT destroy.**
  `4 × 0 = 0` does NOT mean your 4 donuts become 0.
  It means "make 0 groups of 4." You made 0 *new* donuts.
  Your original 4 are still there.
  Lean says it clean: `owned + make_new 0 size = owned`.
  The table counts *new* donuts, not *total* donuts.

- **4 × 0 = 0 does NOT mean 4 = 0.**
  `a * 0 = 0 ∧ a ≠ 0`. The operation result is 0, the input is still not zero.
  Lean won't let you confuse the two — they're two different sides of an `∧`.

- **Zero can never be a denominator.**
  Pressure `= F / A` needs `A > 0`. You can never actually divide by zero to get infinite pressure.
  You pick `A = F / (|P| + F + 1) > 0`, and pressure is huge but finite.

- **Zero as a limit ≠ zero as a state.**
  You can approach 0, but a real atom never *IS* 0.
  If `a₀ > 0`, then `a₀ ≠ 0` and `a₀ * (1 + 1/60) ≠ 0`.
  Absolute zero, zero separation, zero-size point — all limits, never states.

- **Zero does not erase Presence.**
  0 Force = 0 new power, but Presence is still there.
  `presence_volume ≠ 0 ∧ presence_volume + 0 = presence_volume`.

That's why the old multiplication table felt like a lie — it was teaching operation-results as if they were existence. Zero Rules separates them: `owned` vs `make_new`.
