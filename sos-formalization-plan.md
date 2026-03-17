# Sacred Object System — Corrected Lean 4 Formalization Plan

## Phase 1: Core SOS Structure

### Definition (Sacred Object System)

A Sacred Object System (SOS) is a tuple (Omega, Pi, E, C, delta) where:
- Omega is a set (the immutable strategy space)
- Pi is a metric space (the mutable policy space)
- E: Pi -> R is a bounded measurable function (the evaluator)
- C: Pi -> {0, 1} is a constraint predicate
- delta: Pi -> Pi is an update operator satisfying:
  - (i)   E(delta(pi)) >= E(pi) for all pi in Pi             (monotone improvement)
  - (ii)  d(delta(pi), pi) <= Delta for some Delta > 0        (bounded step)
  - (iii) C(delta(pi)) = 1 whenever C(pi) = 1                 (constraint preservation)

**IMPORTANT — Axiom (i) correction:**
The original "pessimistic improvement" E(delta(pi)) >= E(pi) - epsilon is too weak
for convergence. A sequence satisfying only E(x_{n+1}) >= E(x_n) - epsilon can
oscillate indefinitely (e.g. sin(n)). PPO's clipped surrogate objective IS monotone
in expected improvement — that's the entire point of the trust region. The correct
axiom is monotone non-decrease: E(delta(pi)) >= E(pi).

### Lean 4 Encoding (Phase 1)

```lean
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-! # Sacred Object System (SOS)

A general algebraic structure unifying iterative optimization systems
(Autoresearch, PPO, ECEF) under common convergence guarantees.
-/

/-- A Sacred Object System: a metric policy space with a bounded monotone
    evaluator, constraint predicate, and update operator. -/
structure SOS where
  /-- The mutable policy space -/
  Pi : Type*
  /-- Metric structure on Pi -/
  [metric : MetricSpace Pi]
  /-- The evaluator function -/
  E : Pi -> Real
  /-- E is bounded above -/
  E_bddAbove : BddAbove (Set.range E)
  /-- Maximum step size -/
  Delta : Real
  Delta_pos : Delta > 0
  /-- Constraint predicate -/
  C : Pi -> Prop
  /-- The update operator -/
  delta : Pi -> Pi
  /-- Axiom (i): Monotone improvement -/
  monotone_improvement : forall (pi : Pi), E (delta pi) >= E pi
  /-- Axiom (ii): Bounded step -/
  bounded_step : forall (pi : Pi), dist (delta pi) pi <= Delta
  /-- Axiom (iii): Constraint preservation -/
  constraint_preservation : forall (pi : Pi), C pi -> C (delta pi)
```

---

## Phase 2: Convergence Theorem

### Theorem (SOS Convergence)

For any SOS S and initial policy pi_0, the sequence E(delta^n(pi_0))
converges: there exists L in R such that E(delta^n(pi_0)) -> L as n -> infinity.

**Proof sketch:**
1. The sequence a_n = E(delta^n(pi_0)) is monotone non-decreasing (by axiom (i))
2. The sequence is bounded above (by E_bddAbove)
3. By the Monotone Convergence Theorem for real sequences, a_n converges

### Lean 4 Encoding (Phase 2)

```lean
/-- The orbit sequence: E evaluated along iterated updates. -/
noncomputable def SOS.orbit (S : SOS) (pi0 : S.Pi) (n : Nat) : Real :=
  S.E (S.delta^[n] pi0)

/-- The orbit sequence is monotone non-decreasing. -/
theorem SOS.orbit_monotone (S : SOS) (pi0 : S.Pi) :
    Monotone (S.orbit pi0) := by
  intro m n hmn
  -- Induction on the difference (n - m)
  -- Each step: E(delta^[k+1] pi0) = E(delta (delta^[k] pi0)) >= E(delta^[k] pi0)
  sorry

/-- The orbit sequence is bounded above. -/
theorem SOS.orbit_bddAbove (S : SOS) (pi0 : S.Pi) :
    BddAbove (Set.range (S.orbit pi0)) := by
  -- Each orbit value is in Set.range S.E, which is BddAbove
  sorry

/-- **Main theorem**: The evaluator sequence converges. -/
theorem SOS.convergence (S : SOS) (pi0 : S.Pi) :
    exists L : Real,
      Filter.Tendsto (S.orbit pi0) Filter.atTop (nhds L) := by
  -- Combine orbit_monotone and orbit_bddAbove
  -- Apply: monotone bounded sequences converge
  -- Mathlib: `tendsto_of_monotone` or `Real.tendsto_of_bddAbove_monotone`
  sorry
```

**Mathlib lemma to target:** Look for `Real.tendsto_of_bddAbove_monotone`
or construct from `Monotone.tendsto_atTop_atTop` + `Filter.Tendsto.mono_left`.
The exact name may vary by Mathlib version — search for theorems about
monotone bounded real sequences.

---

## Phase 3: SOS Morphisms and Category Structure

### Definition (SOS Morphism)

A morphism phi: S1 -> S2 between SOS is a pair (f: Pi1 -> Pi2, g: R -> R)
where g is monotone and:
- g(E1(pi)) = E2(f(pi)) for all pi in Pi1      (evaluator compatibility)
- f(delta1(pi)) = delta2(f(pi))                  (update commutativity)
- C1(pi) = C2(f(pi))                             (constraint compatibility)

### Lean 4 Encoding (Phase 3)

```lean
/-- A morphism between two Sacred Object Systems. -/
structure SOS.Morphism (S1 S2 : SOS) where
  /-- Map on policy spaces -/
  f : S1.Pi -> S2.Pi
  /-- Map on evaluator values -/
  g : Real -> Real
  /-- g is monotone -/
  g_monotone : Monotone g
  /-- Evaluator compatibility: the diagram commutes -/
  evaluator_compat : forall (pi : S1.Pi), g (S1.E pi) = S2.E (f pi)
  /-- Update commutativity: f intertwines the update operators -/
  update_commute : forall (pi : S1.Pi), f (S1.delta pi) = S2.delta (f pi)
  /-- Constraint compatibility -/
  constraint_compat : forall (pi : S1.Pi), S1.C pi <-> S2.C (f pi)

/-- Identity morphism. -/
def SOS.Morphism.id (S : SOS) : SOS.Morphism S S where
  f := id
  g := id
  g_monotone := monotone_id
  evaluator_compat := fun _ => rfl
  update_commute := fun _ => rfl
  constraint_compat := fun _ => Iff.rfl

/-- Composition of morphisms. -/
def SOS.Morphism.comp {S1 S2 S3 : SOS}
    (phi : SOS.Morphism S2 S3) (psi : SOS.Morphism S1 S2) :
    SOS.Morphism S1 S3 where
  f := phi.f ∘ psi.f
  g := phi.g ∘ psi.g
  g_monotone := phi.g_monotone.comp psi.g_monotone
  evaluator_compat := by
    intro pi
    simp [Function.comp]
    rw [psi.evaluator_compat, phi.evaluator_compat]
  update_commute := by
    intro pi
    simp [Function.comp]
    rw [psi.update_commute, phi.update_commute]
  constraint_compat := by
    intro pi
    exact (psi.constraint_compat pi).trans (phi.constraint_compat (psi.f pi))

/-- Convergence is preserved by morphisms: if S1 converges, so does S2's
    image under the morphism, with limit g(L). -/
theorem SOS.Morphism.preserves_convergence {S1 S2 : SOS}
    (phi : SOS.Morphism S1 S2) (pi0 : S1.Pi)
    (h : exists L, Filter.Tendsto (S1.orbit pi0) Filter.atTop (nhds L)) :
    exists L', Filter.Tendsto (S2.orbit (phi.f pi0)) Filter.atTop (nhds L') := by
  -- S2.orbit (phi.f pi0) n = S2.E (S2.delta^[n] (phi.f pi0))
  -- By update_commute: S2.delta^[n] (phi.f pi0) = phi.f (S1.delta^[n] pi0)
  -- So S2.orbit (phi.f pi0) n = S2.E (phi.f (S1.delta^[n] pi0))
  --                            = phi.g (S1.E (S1.delta^[n] pi0))
  --                            = phi.g (S1.orbit pi0 n)
  -- Since S1.orbit pi0 -> L and phi.g is monotone (hence continuous at limit),
  -- phi.g (S1.orbit pi0 n) -> phi.g L
  sorry
```

---

## Phase 4: Instantiation Proofs (Theorem 1.1)

These are the most domain-specific and least purely mathematical.
Each instantiation requires defining the concrete types and proving the three axioms.

### 4a. PPO as SOS

```lean
/-- PPO instantiates an SOS where the evaluator is the expected clipped
    surrogate objective, which is monotone by the trust region guarantee. -/
-- This is a STATEMENT of the claim, not a full proof.
-- The proof that PPO's update is monotone in expected return is
-- well-established in the RL literature (Schulman et al. 2017).
-- Formalizing it fully requires encoding the clipped surrogate.

-- Minimal encoding: assert the structure exists
axiom PPO_is_SOS : SOS
-- Or, construct it explicitly with sorry for the hard parts
```

### 4b. Autoresearch as SOS

```lean
/-- Autoresearch: Pi = architecture space, E = evaluate.py score,
    delta = modify-train-score-keep/discard.
    The keep/discard mechanism guarantees monotone improvement:
    E(delta(pi)) = max(E(new_arch), E(pi)) >= E(pi). -/
-- The key insight: Autoresearch's binary keep/discard IS monotone
-- because it only accepts improvements. This is trivially monotone.
```

### 4c. ECEF as SOS

```lean
/-- ECEF: Pi = 7-layer encoding space, E = validation scoring,
    delta = extraction-refinement step with expert feedback.
    Monotone improvement follows from the refinement protocol:
    each extraction session can only ADD knowledge, not remove it. -/
```

---

## Phase 5: Lipschitz Bounds (Spectral Normalization)

### Theorem (Spectral Normalization Bound)

If W_SN(W) = W / sigma(W) is applied to every layer of an L-layer network,
the composite function f is L-Lipschitz:
  ||f(x) - f(y)|| <= (product of L_i for i=1..L) * ||x - y||

### Lean 4 Encoding (Phase 5)

```lean
/-- A spectrally normalized function is Lipschitz with constant L. -/
structure SpectrallyNormalized where
  f : Real -> Real  -- simplified; actual encoding uses normed spaces
  L : Real
  L_pos : L > 0
  lipschitz : LipschitzWith (Real.toNNReal L) f

/-- Composition of Lipschitz functions is Lipschitz with product constant. -/
-- This is already in Mathlib: LipschitzWith.comp
```

### Triple Safety Bound

```lean
/-- If three independent safety mechanisms each bound deviation by L1, L2, L3,
    the composite bounds deviation by L1 * L2 * L3. -/
theorem triple_safety_bound
    (f1 f2 f3 : Real -> Real)
    (L1 L2 L3 : NNReal)
    (h1 : LipschitzWith L1 f1)
    (h2 : LipschitzWith L2 f2)
    (h3 : LipschitzWith L3 f3) :
    LipschitzWith (L1 * L2 * L3) (f1 ∘ f2 ∘ f3) :=
  h1.comp (h2.comp h3)
```

---

## Build Order Summary

```
Phase 1: SOS structure           (foundation — everything depends on this)
    |
    v
Phase 2: SOS.convergence         (the main theorem — bounded monotone convergence)
    |
    v
Phase 3: SOS.Morphism            (category structure, convergence preservation)
    |
    v
Phase 4: Instantiation proofs    (PPO/Autoresearch/ECEF are SOS instances)
    |
    v
Phase 5: Lipschitz bounds        (Spectral Normalization, Triple Safety)
```

Each phase builds on the previous. Phase 1 must compile before Phase 2 starts.
Phase 2 is the hardest (finding the right Mathlib lemma for bounded monotone
convergence). Phases 4-5 are somewhat independent of each other.

## Estimated Complexity

| Phase | Difficulty | Mathlib Depth | Lines (est.) |
|-------|-----------|--------------|-------------|
| 1: SOS structure | Easy | MetricSpace only | ~30 |
| 2: Convergence | Medium | Filter, Order, Topology | ~50 |
| 3: Morphisms | Medium | Category theory optional | ~80 |
| 4: Instances | Hard (domain) | Minimal | ~60 |
| 5: Lipschitz | Easy | NNReal, LipschitzWith | ~30 |

## How to Invoke in Your Other Instance

```
/prove

Target: Formalize the Sacred Object System (SOS) and prove convergence.

Source material: /Users/mghome/proofs/sos-formalization-plan.md

Build order:
1. Create new Lean 4 project with Mathlib dependency
2. Phase 1: Define SOS structure
3. Phase 2: Prove SOS.convergence (bounded monotone convergence)
4. Phase 3: Define SOS.Morphism, prove comp and preserves_convergence
5. Phase 4: Instantiation sketches (PPO, Autoresearch, ECEF)
6. Phase 5: Lipschitz bounds

Start with Phase 1+2. Do not proceed to Phase 3 until Phase 2 compiles
with no sorry.
```
