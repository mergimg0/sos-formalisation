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

| Metric | Count |
|--------|-------|
| Theorems | 24 |
| Lemmas | 3 |
| Axioms | 3 (domain-specific, audited) |
| Definitions | 7 |
| Structures | 3 (SOS, SOS.Morphism, SpectrallyNormalized) |
| Lines of Lean 4 | 542 |
| `sorry` declarations | **0** |

## Structure

The formalization is organized in 6 phases in a single file
[`SosFormalization/Basic.lean`](SosFormalization/Basic.lean):

1. **Phase 1** (lines 19–48): Core SOS structure definition
2. **Phase 2** (lines 50–122): Convergence theorem and orbit properties
3. **Phase 3** (lines 124–255): SOS morphisms and category structure
4. **Phase 4** (lines 257–453): Instantiations (PPO, Autoresearch, ECEF) and morphism chain
5. **Phase 5** (lines 455–492): Lipschitz bounds (spectral normalization, triple safety)
6. **Phase 6** (lines 494–542): Policy space convergence and fixed-point theorem

## Key Results

- **Convergence theorem**: For any SOS and initial policy, the evaluator
  orbit converges (`SOS.convergence`)
- **Category structure**: Identity, composition, associativity for SOS
  morphisms (`SOS.Morphism.id_comp`, `comp_id`, `comp_assoc`)
- **Limit transfer**: Convergence propagates across morphisms
  (`SOS.Morphism.preserves_convergence_limit`)
- **Concrete constructions**: Autoresearch (keep/discard) and ECEF
  (append-only refinement) satisfy SOS axioms with no axioms needed
- **Compositional chain**: PPO → Autoresearch → ECEF derived by composition
  (`PPO_to_ECEF_morphism`)
- **Fixed-point theorem**: Continuous update operators converge to stationary
  policies (`SOS.limit_is_fixed_point`)

## Axiom Audit

The formalization contains exactly 3 axioms, each a domain-specific interface
boundary:

1. **`PPO_is_SOS`**: PPO satisfies the SOS axioms (requires formalizing
   trust-region theory)
2. **`PPO_to_Autoresearch_morphism`**: Structure-preserving map from PPO to
   Autoresearch (PPO's policy space is abstract)
3. **`Autoresearch_to_ECEF_morphism`**: Structure-preserving map from
   Autoresearch to ECEF (embedding requires domain-specific semantics)

The PPO → ECEF morphism is **derived by composition**, not axiomatized.

## Building

Requires Lean 4 (v4.28.0) and Mathlib.

```bash
# Get Mathlib cache (recommended, avoids building from source)
lake exe cache get

# Build
lake build
```

Build time with warm Mathlib cache: ~10 seconds.

## Dependencies

- [Lean 4](https://github.com/leanprover/lean4) v4.28.0
- [Mathlib](https://github.com/leanprover-community/mathlib4) v4.28.0
  - `Mathlib.Topology.Order.MonotoneConvergence`
  - `Mathlib.Topology.MetricSpace.Basic`
  - `Mathlib.Topology.MetricSpace.Lipschitz`
  - `Mathlib.Analysis.SpecificLimits.Basic`

## Companion Paper

> M. Gashi, "A Unifying Algebraic Structure for Iterative Optimization with
> Machine-Verified Convergence Guarantees," 2026.

## License

MIT — see [LICENSE](LICENSE).
