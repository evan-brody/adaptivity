# adaptivity

Lean 4 proofs of the adaptivity gap for the Unlimited-Flips Unanimous Vote problem, multiplicative
and additive.

## Verify

```sh
lake build   # succeeds ⟺ both theorems check, no `sorry`
```

First build fetches Mathlib and is slow; later builds are incremental. Single file:
`lake build MulAdaptivityGap` / `lake build AddAdaptivityGap`.

## Where things are

| | [MulAdaptivityGap.lean](MulAdaptivityGap.lean) | [AddAdaptivityGap.lean](AddAdaptivityGap.lean) |
| --- | --- | --- |
| Main theorem | [`adaptivity_gap`:655](MulAdaptivityGap.lean#L655) — `min (C₁, C₂, C₃) ≤ 1.2 * Aₙ` | [`add_adaptivity_gap`:373](AddAdaptivityGap.lean#L373) — `min (C₁, C₂, C₄) ≤ 1/2 + Aₙ` |
| Cost definitions | [`Aₙ`, `C₁`, `C₂`, `C₃`:33-43](MulAdaptivityGap.lean#L33-L43) | [`Aₙ`, `C₁`, `C₂`, `C₄`:28-39](AddAdaptivityGap.lean#L28-L39) |
| Polynomial forms | [`N₃`, `N₆`:45-51](MulAdaptivityGap.lean#L45-L51) | [`L₂`, `L₃`, `L₅`:41-50](AddAdaptivityGap.lean#L41-L50) |
| Polynomial core | [`bound_lower_half`:632](MulAdaptivityGap.lean#L632) | [`polynomial_core`:238](AddAdaptivityGap.lean#L238) |

Both hold on `0 ≤ p₁ ≤ pₙ ≤ 1` with `p₁ + pₙ ≤ 1`.
