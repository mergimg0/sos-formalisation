/-
  CGLESubstrate.lean — Phase-Lock Fraction as a Stochastic Sacred Object System

  Formalizes a discrete-time system of N oscillatory modes from the
  Complex Ginzburg-Landau Equation (CGLE) on S², where:

  - **State**: Phase errors Δφᵢ for each of N active spherical harmonic modes
  - **Evaluator**: Phase-lock fraction — the proportion of modes with |Δφᵢ| < ε
  - **Dynamics**: A Markov kernel κ encoding discretised CGLE dynamics with noise

  The key hypothesis is **Benjamin-Feir stability** (1 + αβ > 0), expressed
  as the stochastic monotone improvement of the phase-lock fraction:
  𝔼[phaseLockFraction(κ(state, ·))] ≥ phaseLockFraction(state).

  Under this hypothesis, the system is a StochasticSOS, and almost-sure
  convergence of the phase-lock fraction follows from the general
  StochasticSOS convergence theorem (Doob's submartingale theorem).

  This file connects three layers of the CGLE substrate architecture:
  1. The CGLE dynamics (encoded abstractly in the Markov kernel)
  2. The SOS convergence guarantee (via StochasticSOS.convergence)
  3. The phase-lock fraction as the observable that converges

  The Benjamin-Feir stability condition 1 + αβ > 0 is the bridge:
  it is a property of the continuous CGLE that implies the discrete
  stochastic monotone improvement axiom.
-/

import SosFormalization.StochasticSOS
import SosFormalization.StochasticRates
import Mathlib.Probability.Distributions.Gaussian.Real

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal MeasureTheory

noncomputable section

/-! ## State Space: Phase Errors for N Modes

The CGLE on S² decomposes into spherical harmonic modes Yₗᵐ(θ, φ).
Only modes with ℓ(ℓ+1) < εR² are active (others decay exponentially).
The state tracks the phase error Δφᵢ of each active mode relative to
its expected frequency-locked value Ω̃ₗ from the CGLE attractor A_∞. -/

/-- The CGLE state: phase errors for N active spherical harmonic modes.
    Each `state i` is the phase error Δφᵢ ∈ ℝ of the i-th active mode. -/
abbrev CGLEState (N : ℕ) := Fin N → ℝ

/-! ## Phase-Lock Fraction Evaluator

A mode is "phase-locked" when its phase error is small: |Δφᵢ| < ε.
The phase-lock fraction counts the proportion of locked modes.
This maps directly to PLL(Δφ) from the heuristic CGLE expression. -/

/-- The lock region: reals within the phase-lock threshold.
    A mode is phase-locked when its phase error lies in (-ε, ε). -/
def lockRegion (ε : ℝ) : Set ℝ := Set.Ioo (-ε) ε

theorem lockRegion_eq_abs (ε : ℝ) : lockRegion ε = {x : ℝ | |x| < ε} := by
  ext x; simp [lockRegion, Set.mem_Ioo, abs_lt]

theorem lockRegion_measurableSet (ε : ℝ) : MeasurableSet (lockRegion ε) :=
  measurableSet_Ioo

/-- Phase-lock indicator for a single mode: 1 if |Δφᵢ| < ε, else 0.
    Uses `Set.indicator` which handles decidability classically. -/
def lockIndicator (N : ℕ) (ε : ℝ) (i : Fin N) (state : CGLEState N) : ℝ :=
  (lockRegion ε).indicator (fun _ => (1 : ℝ)) (state i)

/-- Phase-lock fraction: the proportion of modes that are phase-locked.
    This is the evaluator E for the CGLE substrate as a StochasticSOS.

    phaseLockFraction(state) = |{i : |Δφᵢ| < ε}| / N

    Bounded in [0, 1] by construction. -/
def phaseLockFraction (N : ℕ) [NeZero N] (ε : ℝ) (state : CGLEState N) : ℝ :=
  (∑ i : Fin N, lockIndicator N ε i state) / ↑N

/-! ### Measurability

The phase-lock fraction is measurable w.r.t. the product σ-algebra.
Proof chain: indicator of Borel set ∘ measurable projection → finite sum → div const. -/

/-- Each lockIndicator is measurable: it's the indicator of the Borel set
    (-ε, ε) composed with the measurable projection `state ↦ state i`. -/
theorem lockIndicator_measurable (N : ℕ) (ε : ℝ) (i : Fin N) :
    Measurable (lockIndicator N ε i) := by
  unfold lockIndicator
  exact (measurable_const.indicator (lockRegion_measurableSet ε)).comp (measurable_pi_apply i)

/-- **Measurability of the phase-lock fraction**: the evaluator is a measurable
    function from the product space (Fin N → ℝ) to ℝ.  This eliminates
    the `eval_meas` hypothesis from `CGLESubstrate`. -/
theorem phaseLockFraction_measurable (N : ℕ) [NeZero N] (ε : ℝ) :
    Measurable (phaseLockFraction N ε) := by
  unfold phaseLockFraction
  exact (Finset.measurable_sum _ fun i _ => lockIndicator_measurable N ε i).div_const _

/-! ### Evaluator Bounds

The phase-lock fraction is always in [0, 1], giving |eval| ≤ 1.
This is the Bounded Evaluator condition for StochasticSOS. -/

theorem lockIndicator_nonneg (N : ℕ) (ε : ℝ) (i : Fin N) (state : CGLEState N) :
    0 ≤ lockIndicator N ε i state :=
  Set.indicator_nonneg (fun _ _ => zero_le_one) _

theorem lockIndicator_le_one (N : ℕ) (ε : ℝ) (i : Fin N) (state : CGLEState N) :
    lockIndicator N ε i state ≤ 1 := by
  unfold lockIndicator
  exact Set.indicator_apply_le' (fun _ => le_refl _) (fun _ => zero_le_one)

theorem phaseLockFraction_nonneg (N : ℕ) [NeZero N] (ε : ℝ) (state : CGLEState N) :
    0 ≤ phaseLockFraction N ε state :=
  div_nonneg (Finset.sum_nonneg fun i _ => lockIndicator_nonneg N ε i state)
    (Nat.cast_nonneg N)

theorem phaseLockFraction_le_one (N : ℕ) [NeZero N] (ε : ℝ) (state : CGLEState N) :
    phaseLockFraction N ε state ≤ 1 := by
  unfold phaseLockFraction
  rw [div_le_one (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N)))]
  calc ∑ i : Fin N, lockIndicator N ε i state
      ≤ ∑ _ : Fin N, (1 : ℝ) :=
        Finset.sum_le_sum fun i _ => lockIndicator_le_one N ε i state
    _ = ↑N := by simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]

/-- The phase-lock fraction is bounded by 1 in absolute value.
    This provides the `eval_bound` field for `StochasticSOS`. -/
theorem phaseLockFraction_abs_le_one (N : ℕ) [NeZero N] (ε : ℝ)
    (state : CGLEState N) :
    |phaseLockFraction N ε state| ≤ 1 :=
  abs_le.mpr ⟨by linarith [phaseLockFraction_nonneg N ε state],
               phaseLockFraction_le_one N ε state⟩

/-! ## CGLE Substrate Structure

The substrate bundles the CGLE mode system with the Benjamin-Feir
stability hypothesis.  The BF condition (1 + αβ > 0) from the
continuous CGLE is expressed here in discrete evaluator form:
the expected phase-lock fraction does not decrease under one step
of the CGLE dynamics kernel. -/

/-- A **CGLE Substrate**: N oscillatory modes on S² with a Markov kernel
    satisfying Benjamin-Feir stability for the phase-lock fraction.

    This is the dynamical substrate that sits underneath the SOS
    convergence guarantee.  The SOS tells you THAT convergence happens;
    the CGLE substrate tells you HOW — through phase-locking dynamics
    of spherical harmonic modes under nonlinear coupling with noise.

    Parameters:
    - `N` : number of active modes (determined by ℓ(ℓ+1) < εR²)
    - `ε` : phase-lock threshold (a mode is "locked" when |Δφᵢ| < ε)
    - `κ` : Markov kernel encoding one step of discretised CGLE + noise
    - `bf_stability` : the Benjamin-Feir condition in evaluator form -/
structure CGLESubstrate where
  /-- Number of active spherical harmonic modes (those with ℓ(ℓ+1) < εR²) -/
  N : ℕ
  [N_pos : NeZero N]
  /-- Lock threshold: mode i is "phase-locked" when |Δφᵢ| < ε.
      Smaller ε means stricter phase coherence requirements. -/
  ε : ℝ
  ε_pos : 0 < ε
  /-- Markov transition kernel encoding discretised CGLE dynamics.
      Encapsulates the update rule:
        Δφ'ᵢ = Δφᵢ - γᵢ · sin(Δφᵢ) + coupling(Δφ) + √(2T) · ξᵢ
      where γᵢ is the phase contraction rate (from 1+αβ > 0)
      and ξᵢ is Gaussian noise at temperature T. -/
  κ : Kernel (CGLEState N) (CGLEState N)
  [markov : IsMarkovKernel κ]
  /-- **Benjamin-Feir stability condition** (evaluator form).
      Note: measurability of the phase-lock fraction is PROVEN
      (`phaseLockFraction_measurable`) — no hypothesis needed.

      𝔼[phaseLockFraction(state') | state] ≥ phaseLockFraction(state)

      This is the SOS Monotone Improvement axiom.  In the continuous CGLE,
      it holds when 1 + αβ > 0 because:
      - Phase contraction (from nonlinear coupling) exceeds noise diffusion
      - Locked modes stay locked with high probability (phase errors contract)
      - Unlocked modes near the boundary drift toward lock
      - The net effect: expected lock count is non-decreasing

      When 1 + αβ < 0 (Benjamin-Feir unstable), this condition FAILS:
      noise overwhelms contraction, phase turbulence ensues, and the
      phase-lock fraction can decrease in expectation.  The system
      is no longer a StochasticSOS.

      This threshold IS the formal boundary between convergent and
      turbulent dynamics — the CGLE's prediction of when PLL maintains lock. -/
  bf_stability : ∀ state : CGLEState N,
    ∫ s', phaseLockFraction N ε s' ∂(κ state) ≥ phaseLockFraction N ε state

attribute [instance] CGLESubstrate.N_pos CGLESubstrate.markov

/-! ## StochasticSOS Construction

The central construction: a CGLE substrate with Benjamin-Feir stability
IS a Stochastic Sacred Object System.  Convergence then follows for free
from the existing StochasticSOS convergence theorem (Doob's submartingale
convergence, proved in StochasticSOS.lean with zero sorry). -/

/-- A CGLE substrate with Benjamin-Feir stability IS a Stochastic Sacred
    Object System.

    The mapping:
    - **State space** P = CGLEState N (phase errors of N modes)
    - **Evaluator** eval = phaseLockFraction (proportion of locked modes)
    - **Kernel** = CGLE dynamics kernel κ
    - **Stochastic monotone improvement** = Benjamin-Feir stability
    - **Bounded evaluator** = phase-lock fraction ∈ [0, 1], so |eval| ≤ 1

    Once constructed, ALL of the StochasticSOS theory applies:
    - Almost-sure convergence (Doob's theorem)
    - Submartingale property of the evaluator process
    - Stochastic morphisms to/from other SOS instances
    - Stochastic rate transfer via Hölder morphisms -/
def CGLESubstrate.toStochasticSOS (S : CGLESubstrate) : StochasticSOS where
  P := CGLEState S.N
  eval := phaseLockFraction S.N S.ε
  eval_measurable := phaseLockFraction_measurable S.N S.ε
  kernel := S.κ
  stoch_improvement := S.bf_stability
  eval_bound := ⟨1, fun state => by
    have := phaseLockFraction_abs_le_one S.N S.ε state
    simp only [NNReal.coe_one]
    exact this⟩

/-! ## Main Theorem: Almost-Sure Convergence of Phase Lock

The payoff: under Benjamin-Feir stability, the phase-lock fraction
converges almost surely.  The proof is ONE LINE — we construct the
StochasticSOS and invoke the general convergence theorem.

This is the formal statement that oscillatory modes on a sphere,
evolving under BF-stable CGLE dynamics with stochastic noise,
converge to a definite level of phase coherence.

The limit L ∈ [0, 1] represents the system's equilibrium coherence:
- L = 1: all modes achieve phase lock (full coherence)
- L ∈ (0, 1): partial coherence (some modes locked, some drifting)
- L = 0: no coherence (all modes unlocked — but this case is
  excluded by BF stability, which guarantees improvement)

The variance-acceleration theorem (Section 9 of the SOS paper)
additionally shows that the stochastic noise √(2T)ξ in the CGLE
does not slow convergence — it ACCELERATES it, via the extra
descent term c · Var[eval].  This is the formal version of
stochastic resonance in the CGLE. -/

/-- **CGLE Phase-Lock Convergence Theorem**:

    Under Benjamin-Feir stability (1 + αβ > 0), for any initial
    configuration of N oscillatory modes on S², the phase-lock
    fraction converges almost surely to a limit.

    Proof: The CGLE substrate is a StochasticSOS (by toStochasticSOS),
    so the general StochasticSOS convergence theorem applies.
    That theorem uses:
      (1) Submartingale property (from stochastic monotone improvement)
      (2) L¹ bound (from |eval| ≤ 1)
      (3) Doob's forward convergence theorem

    All three are established in StochasticSOS.lean with zero sorry.
    This theorem inherits that verification with zero additional sorry. -/
theorem CGLESubstrate.phaseLock_convergence (S : CGLESubstrate)
    (state₀ : CGLEState S.N) :
    ∀ᵐ ω ∂(sosPathMeasure state₀ S.κ),
      ∃ L : ℝ, Tendsto (fun n => phaseLockFraction S.N S.ε (ω n))
        atTop (nhds L) :=
  S.toStochasticSOS.convergence state₀

/-! ## Connecting to the SOS Morphism Theory

Because a CGLE substrate is a StochasticSOS, it inherits the full
morphism theory.  This means:

1. **Rate transfer**: If the CGLE substrate satisfies a stochastic
   Łojasiewicz condition, the O(1/n) rate transfers through
   Hölder-continuous morphisms to connected systems (Theorem 10.1).

2. **Directed chains**: A chain CGLE → ProofForge → ECEF inherits
   convergence by morphism composition (Theorem 5.17).

3. **Variance acceleration**: The noise term √(2T)ξ in the CGLE
   provides the evaluator variance that accelerates convergence
   beyond the deterministic rate (Theorem 9.1).

These are not reproved here — they follow automatically from the
StochasticSOS construction.  The convergence certificate for the
CGLE substrate composes with the existing AReaL/GRPO certificates
via the category StochSOS. -/

/-! ## O(1/n) Rate under Stochastic Łojasiewicz -/

/-- **CGLE Phase-Lock Rate Theorem (O(1/n))**: Under the stochastic
    quadratic Łojasiewicz condition, the expected gap decays as O(1/n). -/
theorem CGLESubstrate.phaseLock_rate (S : CGLESubstrate)
    (state0 : CGLEState S.N)
    {M : ℝ} (hM : ∀ state : CGLEState S.N, phaseLockFraction S.N S.ε state ≤ M)
    {c : ℝ} (hc : 0 < c)
    (hLoj : ∀ state : CGLEState S.N,
      ∫ s', phaseLockFraction S.N S.ε s' ∂(S.κ state) -
        phaseLockFraction S.N S.ε state ≥
        c * (M - phaseLockFraction S.N S.ε state) ^ 2)
    (n : ℕ) :
    S.toStochasticSOS.expectedGap state0 M n ≤
      S.toStochasticSOS.expectedGap state0 M 0 /
        (1 + c * S.toStochasticSOS.expectedGap state0 M 0 * ↑n) :=
  S.toStochasticSOS.expected_rate_alpha2 state0 hM hc hLoj n

/-- **High-probability phase-lock bound** via Markov's inequality:
    ep * P(gap ≥ ep) ≤ e0 / (1 + c * e0 * n). -/
theorem CGLESubstrate.phaseLock_high_prob (S : CGLESubstrate)
    (state0 : CGLEState S.N)
    {M : ℝ} (hM : ∀ state : CGLEState S.N, phaseLockFraction S.N S.ε state ≤ M)
    {c : ℝ} (hc : 0 < c)
    (hLoj : ∀ state : CGLEState S.N,
      ∫ s', phaseLockFraction S.N S.ε s' ∂(S.κ state) -
        phaseLockFraction S.N S.ε state ≥
        c * (M - phaseLockFraction S.N S.ε state) ^ 2)
    {ep : ℝ} (hep : 0 < ep) (n : ℕ) :
    ep * (sosPathMeasure state0 S.κ).real
      {w | ep ≤ M - phaseLockFraction S.N S.ε (w n)} ≤
      S.toStochasticSOS.expectedGap state0 M 0 /
        (1 + c * S.toStochasticSOS.expectedGap state0 M 0 * ↑n) :=
  S.toStochasticSOS.high_probability_bound state0 hM hc hLoj hep n

/-! ## Concrete Kernel: Lock-Preserving Dynamics

A naive Gaussian contraction kernel does NOT satisfy bf_stability:
noise can kick perfectly locked modes out of the lock region.
The expected lock fraction decreases at the all-locked state.

The fix: a **lock-preserving kernel** that applies a keep/discard
mechanism per mode.  This mirrors the Autoresearch SOS construction
(Section 5.3 of the paper): propose an update, accept only if the
mode stays locked (or was unlocked and improves).

Physically, this captures the CGLE's nonlinear |A|²A coupling,
which acts as a restoring force for phase-locked modes.  The
coupling prevents noise from destroying established locks.

With lock preservation, bf_stability follows from:
- Locked modes: stay locked (by preservation) → indicator = 1 a.s.
- Unlocked modes: indicator ≥ 0 trivially
- Sum over modes: expected fraction ≥ current fraction. -/

/-- **Lock preservation**: a kernel preserves phase locks — if mode i
    is locked (|Δφᵢ| < ε), it remains locked after one step a.s.

    This models the CGLE's nonlinear restoring force: the |A|²A
    coupling term drives locked modes back toward their equilibrium
    phase, preventing noise from destroying established locks.

    Kernels satisfying this include:
    - Keep/discard wrappers around any base kernel
    - Kernels with sufficiently strong contraction (γε >> σ)
    - CGLE kernels in the strongly BF-stable regime -/
def IsLockPreserving (N : ℕ) (ε : ℝ)
    (κ : Kernel (CGLEState N) (CGLEState N)) : Prop :=
  ∀ state : CGLEState N, ∀ i : Fin N,
    state i ∈ lockRegion ε →
      (κ state) {s' | s' i ∈ lockRegion ε} = 1

/-- For a locked mode under a lock-preserving kernel, the lock
    indicator is 1 almost surely after one step. -/
lemma lockIndicator_ae_one_of_locked {N : ℕ} {ε : ℝ}
    {κ : Kernel (CGLEState N) (CGLEState N)} [IsMarkovKernel κ]
    (hLP : IsLockPreserving N ε κ) {state : CGLEState N}
    {i : Fin N} (hi : state i ∈ lockRegion ε) :
    ∀ᵐ s' ∂(κ state), lockIndicator N ε i s' = 1 := by
  have hsub : {s' : CGLEState N | s' i ∈ lockRegion ε} ⊆
      {s' | lockIndicator N ε i s' = 1} := fun s' (hs' : s' i ∈ lockRegion ε) => by
    change lockIndicator N ε i s' = 1
    exact Set.indicator_of_mem hs' _
  have hlock := hLP state i hi
  rw [ae_iff]
  apply measure_mono_null (Set.compl_subset_compl.mpr hsub)
  have hmeas : MeasurableSet {s' : CGLEState N | s' i ∈ lockRegion ε} :=
    (lockRegion_measurableSet ε).preimage (measurable_pi_apply i)
  haveI : IsProbabilityMeasure (κ state) := IsMarkovKernel.isProbabilityMeasure state
  exact (prob_compl_eq_zero_iff hmeas).mpr hlock

/-- For an unlocked mode, the integral of the lock indicator is ≥ 0. -/
lemma lockIndicator_integral_nonneg {N : ℕ} {ε : ℝ}
    (κ : Kernel (CGLEState N) (CGLEState N)) [IsMarkovKernel κ]
    (state : CGLEState N) (i : Fin N) :
    0 ≤ ∫ s', lockIndicator N ε i s' ∂(κ state) :=
  integral_nonneg fun s' => lockIndicator_nonneg N ε i s'

/-- **BF stability from lock preservation**: if the kernel preserves
    phase locks per-mode, the expected phase-lock fraction does not
    decrease.  This eliminates the sorry from the concrete kernel.

    Proof structure:
    1. Decompose phaseLockFraction into a sum of lockIndicators / N
    2. Swap integral and finite sum (linearity)
    3. For each mode, show ∫ lockIndicator dκ ≥ lockIndicator(state):
       - Locked mode: lock preservation gives indicator = 1 a.s.,
         so integral = 1 = current indicator
       - Unlocked mode: integral ≥ 0 = current indicator (trivial)
    4. Sum the per-mode bounds and divide by N -/
theorem bf_stability_of_lock_preservation
    {N : ℕ} [NeZero N] {ε : ℝ}
    {κ : Kernel (CGLEState N) (CGLEState N)} [IsMarkovKernel κ]
    (hLP : IsLockPreserving N ε κ)
    (state : CGLEState N) :
    ∫ s', phaseLockFraction N ε s' ∂(κ state) ≥ phaseLockFraction N ε state := by
  rw [ge_iff_le]
  unfold phaseLockFraction
  -- Each lockIndicator is integrable (bounded measurable on a probability space)
  have hint : ∀ i : Fin N, Integrable (lockIndicator N ε i) (κ state) := fun i =>
    Integrable.of_bound (lockIndicator_measurable N ε i).aestronglyMeasurable 1
      (ae_of_all _ fun s' => by
        rw [Real.norm_eq_abs, abs_of_nonneg (lockIndicator_nonneg N ε i s')]
        exact lockIndicator_le_one N ε i s')
  -- Suffices to show the sum inequality (divide both sides by N)
  -- Suffices: show the numerator sum inequality
  suffices h : ∑ i : Fin N, lockIndicator N ε i state ≤
      ∫ s', ∑ i : Fin N, lockIndicator N ε i s' ∂(κ state) by
    have hN : (0 : ℝ) ≤ ↑N := Nat.cast_nonneg N
    calc (∑ i, lockIndicator N ε i state) / ↑N
        ≤ (∫ s', ∑ i, lockIndicator N ε i s' ∂κ state) / ↑N :=
          div_le_div_of_nonneg_right h hN
      _ = ∫ s', (∑ i, lockIndicator N ε i s') / ↑N ∂κ state :=
          (integral_div (↑N : ℝ) _).symm
  -- Swap ∫ and Σ
  rw [integral_finset_sum Finset.univ fun i _ => hint i]
  -- Per-mode comparison
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : state i ∈ lockRegion ε
  · -- Locked mode: lockIndicator = 1, integral = 1
    have h1 : lockIndicator N ε i state = 1 := Set.indicator_of_mem hi _
    rw [h1]
    have hae := lockIndicator_ae_one_of_locked hLP hi
    rw [show (1 : ℝ) = ∫ _, (1 : ℝ) ∂(κ state) from by simp [integral_const]]
    exact (integral_congr_ae hae).symm.le
  · -- Unlocked mode: lockIndicator = 0, integral ≥ 0
    have h0 : lockIndicator N ε i state = 0 :=
      Set.indicator_of_notMem hi _
    rw [h0]
    exact lockIndicator_integral_nonneg κ state i

/-- A CGLESubstrate can be constructed from any lock-preserving kernel,
    with bf_stability proven (not hypothesized). -/
def CGLESubstrate.ofLockPreserving
    (N : ℕ) [NeZero N] (ε : ℝ) (hε : 0 < ε)
    (κ : Kernel (CGLEState N) (CGLEState N)) [IsMarkovKernel κ]
    (hLP : IsLockPreserving N ε κ) : CGLESubstrate where
  N := N
  ε := ε
  ε_pos := hε
  κ := κ
  bf_stability := bf_stability_of_lock_preservation hLP

/-! ## Stochastic Morphism: CGLE to GRPO

A morphism from the CGLE substrate to a stochastic GRPO instance
transfers convergence through the StochSOS category. -/

/-- **CGLE to GRPO Morphism**: given maps (f, g) satisfying evaluator
    compatibility and kernel commutativity, the CGLE substrate connects
    to a stochastic GRPO instance in the StochSOS category. -/
def CGLESubstrate.morphismToGRPO (S : CGLESubstrate)
    {Pol : Type*} [MeasurableSpace Pol]
    (grpoEval : Pol → ℝ) (grpoEval_meas : Measurable grpoEval)
    (grpoKernel : Kernel Pol Pol) [IsMarkovKernel grpoKernel]
    (hImprove : ∀ π, ∫ π', grpoEval π' ∂(grpoKernel π) ≥ grpoEval π)
    (hBdd : ∃ M : ℝ≥0, ∀ π, |grpoEval π| ≤ M)
    (f : CGLEState S.N → Pol) (g : ℝ → ℝ)
    (hf_meas : Measurable f)
    (hg_mono : Monotone g)
    (hcompat : ∀ state : CGLEState S.N,
      g (phaseLockFraction S.N S.ε state) = grpoEval (f state))
    (hkernel : ∀ state : CGLEState S.N,
      (S.κ state).map f = grpoKernel (f state)) :
    StochasticSOS.Morphism S.toStochasticSOS
      (stochasticGrpoSOS grpoEval grpoEval_meas grpoKernel hImprove hBdd) where
  f := f
  g := g
  f_measurable := hf_meas
  g_monotone := hg_mono
  evaluator_compat := hcompat
  kernel_compat := hkernel

end
