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
| Main theorem | [`mul_adaptivity_gap`:663](MulAdaptivityGap.lean#L663) — `min (C₁, C₂, C₃) ≤ 1.2 * Aₙ` | [`add_adaptivity_gap`:394](AddAdaptivityGap.lean#L394) — `min (C₁, C₂, C₄) ≤ 1/2 + Aₙ` |
| Cost definitions | [`Aₙ`, `C₁`, `C₂`, `C₃`:42-49](MulAdaptivityGap.lean#L42-L49) | [`Aₙ`, `C₁`, `C₂`, `C₄`:37-48](AddAdaptivityGap.lean#L37-L48) |
| Polynomial forms | [`N₃`, `N₆`:53-58](MulAdaptivityGap.lean#L53-L58) | [`L₂`, `L₃`, `L₅`:50-59](AddAdaptivityGap.lean#L50-L59) |
| Polynomial core | [`bound_lower_half`:640](MulAdaptivityGap.lean#L640) | [`polynomial_core`:250](AddAdaptivityGap.lean#L250) |

Both hold on `0 ≤ p₁ ≤ pₙ ≤ 1` with `p₁ + pₙ ≤ 1`.
