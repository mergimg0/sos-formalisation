# Sacred Object System — Lean 4 Formalization

Machine-verified formalization of the Sacred Object System (SOS), a unifying
algebraic structure for iterative optimization with convergence guarantees.

## Overview

A sacred object system is a metric policy space equipped with a bounded
evaluator, a step-bounded update operator, and a constraint predicate.
From three axioms — monotone improvement, bounded step, constraint
preservation — convergence of the evaluator sequence follows as a free
theorem via the Monotone Convergence Theorem.

## Formalization Statistics

| File | Lines | Declarations | sorry |
|------|------:|:------------:|:-----:|
| Basic.lean | 1,261 | 79 | 0 |
| PowerLaw.lean | 604 | 22 | 0 |
| StochasticSOS.lean | 386 | 21 | 0 |
| AReaL.lean | 347 | 16 | 0 |
| StochasticRates.lean | 1,558 | 50+ | 0 |
| **Total** | **4,229** | **200+** | **0** |

## File Structure

### Basic.lean (1,261 lines)
Core SOS framework:
- SOS structure definition and convergence theorem
- SOS morphisms with category structure (identity, composition, associativity)
- Rate theory: geometric rates under linear Łojasiewicz conditions
- Lipschitz rate transfer for morphisms
- Concrete instantiations (PPO, Autoresearch, ECEF)
- Fixed-point theorem for continuous update operators

### StochasticSOS.lean (386 lines)
Stochastic extension:
- Stochastic SOS with Markov kernel updates
- Submartingale property of the evaluator process
- Almost-sure convergence via Doob's theorem
- Stochastic morphisms with category structure
- Embedding of deterministic SOS into stochastic SOS

### PowerLaw.lean (604 lines)
Power-law convergence rates (sequel paper):
- Quadratic Łojasiewicz (α = 2): O(1/n) rate via multiplication-form induction
- General Łojasiewicz (α = p+1 ≥ 2): O(1/n) rate on gap^p via Bernoulli product inequality
- Hölder rate transfer: morphism regularity controls rate distortion
- Gradient descent as a concrete SOS with O(1/n) rate as a free theorem

### AReaL.lean (347 lines)
AReaL integration (async RL):
- GRPO as a concrete SOS (no axioms) — the DeepSeek R1 algorithm
- Doubly constraint-lifted SOS for async training (staleness + M2PO)
- Decoupled PPO via constraint lifting (no new axioms)
- Quadruple safety Lipschitz bound

### StochasticRates.lean (1,558 lines)
Stochastic convergence rates:
- Standalone algebraic rate lemma (reusable across deterministic + stochastic)
- Jensen bridge: stochastic O(1/n) rate via tower property + Jensen's inequality
- General α stochastic rates via ConvexOn.map_average_le
- Pathwise O(1/n) rate and pathwise Hölder transfer
- Expected Hölder transfer via ConcaveOn.le_map_average
- High-probability (Markov inequality) bound
- Stochastic GRPO, autoresearch, SGD constructions
- Kernel mixture preservation (Edge 7: interruptible generation)
- ε-Approximate lax morphisms (Edge 8: proximal interpolation)
- KDRL warm-start rate transfer (Edge 6)
- Stochastic constraint lifting via Kernel.piecewise

## Paper-to-Code Mapping (Sequel Paper)

| Paper Theorem | Lean Identifier | Description |
|:---:|:---|:---|
| Thm 3.2 | `SOS.power_law_rate_alpha2` | O(1/n) rate for α = 2 |
| Thm 3.3 | `SOS.local_power_law_rate_alpha2` | Basin-restricted α = 2 rate |
| Rem 3.3 | `SOS.loj_implies_small` | Small-constant condition derivable |
| Lem 3.5 | `bernoulli_product` | (1 + pt)(1-t)^p ≤ 1 |
| Thm 3.6 | `SOS.power_law_rate_general` | General α rate |
| Thm 4.1 | `SOS.Morphism.holder_rate_transfer_alpha2` | Hölder transfer, α = 2 |
| Thm 4.2 | `SOS.Morphism.local_holder_rate_transfer_alpha2` | Local Hölder transfer |
| Thm 4.3 | `SOS.Morphism.holder_rate_transfer_general` | Hölder transfer, general α |
| Cor 4.4 | `SOS.Morphism.lipschitz_rate_transfer_alpha2` | Lipschitz transfer, α = 2 |
| Def 5.1 | `gradientDescentSOS` | GD-SOS construction |
| Thm 5.2 | `gd_convergence` | GD convergence (free theorem) |
| Thm 5.3 | `gd_rate` | GD O(1/n) rate |

## Axiom Audit

The formalization contains exactly 3 domain-specific axioms (in Basic.lean),
each an interface boundary:

1. **`PPO_is_SOS`**: PPO satisfies the SOS axioms
2. **`PPO_to_Autoresearch_morphism`**: Structure-preserving map PPO → Autoresearch
3. **`Autoresearch_to_ECEF_morphism`**: Structure-preserving map Autoresearch → ECEF

PowerLaw.lean and StochasticSOS.lean introduce **zero** new axioms.
The GD-SOS construction uses hypothesis parameters, not axioms.

## Building

Requires Lean 4 (v4.28.0) and Mathlib.

```bash
# Get Mathlib cache (recommended, avoids building from source)
lake exe cache get

# Build
lake build
```

Build time with warm Mathlib cache: ~20 seconds (1,965 elaboration jobs).

## Dependencies

- [Lean 4](https://github.com/leanprover/lean4) v4.28.0
- [Mathlib](https://github.com/leanprover-community/mathlib4) v4.28.0

Key Mathlib imports:
- `Mathlib.Topology.Order.MonotoneConvergence`
- `Mathlib.Topology.MetricSpace.Basic`
- `Mathlib.Topology.MetricSpace.Lipschitz`
- `Mathlib.Analysis.SpecialFunctions.Pow.Real` (PowerLaw.lean only)
- `Mathlib.Probability.Kernel.Basic` (StochasticSOS.lean only)

## Companion Papers

> M. Gashi, "The Sacred Object System: Convergence as a Free Theorem for
> Iterative Optimization," submitted to CPP 2027, 2026.

> M. Gashi, "Power-Law Convergence Rates for Sacred Object Systems with
> Hölder Rate Transfer," submitted to CPP 2027, 2026.

## License

MIT — see [LICENSE](LICENSE).
