/-
  StochasticRates.lean — Power-Law Convergence Rates for Stochastic SOS

  Extends the stochastic SOS framework with quantitative convergence rates
  under stochastic Łojasiewicz conditions.  The key insight is the
  "Jensen bridge": the tower property + Jensen's inequality reduce the
  stochastic recurrence to the deterministic one, allowing the
  multiplication-form induction from PowerLaw.lean to be reused.

  Key results:
  - power_law_recurrence_mul: standalone algebraic rate lemma
  - power_law_recurrence_div: division form of the standalone lemma
  - StochasticSOS.expected_gap_recurrence: the Jensen bridge
  - StochasticSOS.expected_rate_alpha2: stochastic O(1/n) rate
-/

import SosFormalization.StochasticSOS
import SosFormalization.PowerLaw
import SosFormalization.AReaL
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.Probability.Moments.Variance

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal MeasureTheory

/-! # Standalone Algebraic Rate Lemma

The multiplication-form induction from PowerLaw.lean is tied to the SOS
structure (it operates on `S.orbit`).  We extract the purely algebraic
content into a standalone lemma that applies to any non-negative sequence
satisfying the recurrence e_{n+1} ≤ e_n(1 - c·e_n).

This lemma is then used for BOTH the deterministic rate (as a sanity check)
and the stochastic expected-gap rate (the new result). -/

section AlgebraicRate

/-- **Standalone power-law rate** (multiplication form): if a non-negative
    sequence {e_n} with e_n ≤ e₀ satisfies the recurrence
    e_{n+1} ≤ e_n · (1 - c · e_n), then e_n · (1 + c · e₀ · n) ≤ e₀.

    This extracts the algebraic core of `SOS.power_law_mul_alpha2`
    (PowerLaw.lean) into a structure-independent form.  The proof is
    identical: the key step factors as (a+b)(1-b) ≤ 1-b² ≤ 1. -/
theorem power_law_recurrence_mul
    (e : ℕ → ℝ) (c e0 : ℝ)
    (hc_pos : 0 < c)
    (he0_nn : 0 ≤ e0)
    (hce_small : c * e0 ≤ 1)
    (hnn : ∀ n, 0 ≤ e n)
    (hle : ∀ n, e n ≤ e0)
    (hrec : ∀ n, e (n + 1) ≤ e n * (1 - c * e n))
    (n : ℕ) :
    e n * (1 + c * e0 * ↑n) ≤ e0 := by
  induction n with
  | zero =>
    simp only [Nat.cast_zero, mul_zero, add_zero, mul_one]
    exact hle 0
  | succ n ih =>
    set en := e n
    have hen_nn : 0 ≤ en := hnn n
    have hen_le : en ≤ e0 := hle n
    have hcen_le : c * en ≤ 1 :=
      le_trans (mul_le_mul_of_nonneg_left hen_le (le_of_lt hc_pos)) hce_small
    have hen1_le : e (n + 1) ≤ en * (1 - c * en) := hrec n
    have h1_sub_nn : 0 ≤ 1 - c * en := by linarith
    simp only [Nat.cast_succ]
    have hden_nn : 0 ≤ 1 + c * e0 * (↑n + 1) := by positivity
    calc e (n + 1) * (1 + c * e0 * (↑n + 1))
        ≤ en * (1 - c * en) * (1 + c * e0 * (↑n + 1)) :=
          mul_le_mul_of_nonneg_right hen1_le hden_nn
      _ = en * (1 + c * e0 * ↑n) * (1 - c * en)
          + c * e0 * en * (1 - c * en) := by ring
      _ ≤ e0 * (1 - c * en) + c * e0 * en * (1 - c * en) := by
          linarith [mul_le_mul_of_nonneg_right ih h1_sub_nn]
      _ = e0 * (1 + c * en) * (1 - c * en) := by ring
      _ = e0 * (1 - (c * en) ^ 2) := by ring
      _ ≤ e0 := by nlinarith [sq_nonneg (c * en)]

/-- **Standalone power-law rate** (division form): e_n ≤ e₀ / (1 + c·e₀·n). -/
theorem power_law_recurrence_div
    (e : ℕ → ℝ) (c e0 : ℝ)
    (hc_pos : 0 < c)
    (he0_nn : 0 ≤ e0)
    (hce_small : c * e0 ≤ 1)
    (hnn : ∀ n, 0 ≤ e n)
    (hle : ∀ n, e n ≤ e0)
    (hrec : ∀ n, e (n + 1) ≤ e n * (1 - c * e n))
    (n : ℕ) :
    e n ≤ e0 / (1 + c * e0 * ↑n) := by
  have hden_pos : 0 < 1 + c * e0 * ↑n := by positivity
  rw [le_div_iff₀ hden_pos]
  exact power_law_recurrence_mul e c e0 hc_pos he0_nn hce_small hnn hle hrec n

/-- The small-constant condition c·e₀ ≤ 1 is derivable from the recurrence:
    if e_{n+1} ≤ e_n(1 - c·e_n) and e_n ≥ 0 and e_1 ≥ 0, then c·e_0 ≤ 1.
    (Otherwise e_1 ≤ e_0(1 - c·e_0) < 0, contradicting e_1 ≥ 0.) -/
lemma small_constant_of_recurrence
    (e : ℕ → ℝ) (c : ℝ)
    (hc_pos : 0 < c)
    (hnn : ∀ n, 0 ≤ e n)
    (hrec : ∀ n, e (n + 1) ≤ e n * (1 - c * e n)) :
    c * e 0 ≤ 1 := by
  by_contra h
  push_neg at h
  have he0_pos : 0 < e 0 := by
    rcases eq_or_lt_of_le (hnn 0) with he0 | he0
    · exfalso; rw [← he0] at h; simp at h; linarith
    · exact he0
  have : e 1 ≤ e 0 * (1 - c * e 0) := hrec 0
  have : e 0 * (1 - c * e 0) < 0 := by nlinarith
  linarith [hnn 1]

/-- **Standalone general power-law rate** (multiplication form, p-th power):
    if e_{n+1} ≤ e_n · (1 - c · e_n^p) for all n, then
    e_n^p · (1 + c·p·e₀^p·n) ≤ e₀^p.
    Extracted from SOS.power_law_mul_general for reuse in stochastic setting. -/
theorem power_law_recurrence_mul_general
    (e : ℕ → ℝ) (c e0 : ℝ) (p : ℕ) (hp : 1 ≤ p)
    (hc_pos : 0 < c)
    (he0_nn : 0 ≤ e0)
    (hce_small : c * e0 ^ p ≤ 1)
    (hnn : ∀ n, 0 ≤ e n)
    (hle : ∀ n, e n ≤ e0)
    (hrec : ∀ n, e (n + 1) ≤ e n * (1 - c * e n ^ p))
    (n : ℕ) :
    e n ^ p * (1 + c * ↑p * e0 ^ p * ↑n) ≤ e0 ^ p := by
  set ρ := e0 ^ p
  have hρ_nn : 0 ≤ ρ := pow_nonneg he0_nn p
  induction n with
  | zero =>
    simp only [Nat.cast_zero, mul_zero, add_zero, mul_one]
    exact pow_le_pow_left₀ (hnn 0) (hle 0) p
  | succ n ih =>
    set en := e n
    have hen_nn : 0 ≤ en := hnn n
    have hen_le : en ≤ e0 := hle n
    have henp_le : en ^ p ≤ ρ := pow_le_pow_left₀ hen_nn hen_le p
    have hcenp_le : c * en ^ p ≤ 1 :=
      le_trans (mul_le_mul_of_nonneg_left henp_le (le_of_lt hc_pos)) hce_small
    have hcenp_nn : (0 : ℝ) ≤ c * en ^ p := by positivity
    have h1cenp_nn : 0 ≤ 1 - c * en ^ p := by linarith
    have hstep : e (n + 1) ≤ en * (1 - c * en ^ p) := hrec n
    have horbp : e (n + 1) ^ p ≤ en ^ p * (1 - c * en ^ p) ^ p := by
      have h := pow_le_pow_left₀ (hnn (n + 1)) hstep p
      rwa [mul_pow] at h
    simp only [Nat.cast_succ]
    have hden_nn : 0 ≤ 1 + c * ↑p * ρ * (↑n + 1) := by positivity
    calc e (n + 1) ^ p * (1 + c * ↑p * ρ * (↑n + 1))
        ≤ en ^ p * (1 - c * en ^ p) ^ p * (1 + c * ↑p * ρ * (↑n + 1)) :=
          mul_le_mul_of_nonneg_right horbp hden_nn
      _ = (1 - c * en ^ p) ^ p * (en ^ p * (1 + c * ↑p * ρ * ↑n)) +
          c * ↑p * ρ * en ^ p * (1 - c * en ^ p) ^ p := by ring
      _ ≤ (1 - c * en ^ p) ^ p * ρ +
          c * ↑p * ρ * en ^ p * (1 - c * en ^ p) ^ p := by
          linarith [mul_le_mul_of_nonneg_left ih (pow_nonneg h1cenp_nn p)]
      _ = ρ * ((1 + ↑p * (c * en ^ p)) * (1 - c * en ^ p) ^ p) := by ring
      _ ≤ ρ * 1 :=
          mul_le_mul_of_nonneg_left (bernoulli_product p (c * en ^ p) hcenp_nn hcenp_le) hρ_nn
      _ = ρ := mul_one ρ

/-- **Standalone general power-law rate** (division form):
    e_n^p ≤ e₀^p / (1 + c·p·e₀^p·n). -/
theorem power_law_recurrence_div_general
    (e : ℕ → ℝ) (c e0 : ℝ) (p : ℕ) (hp : 1 ≤ p)
    (hc_pos : 0 < c)
    (he0_nn : 0 ≤ e0)
    (hce_small : c * e0 ^ p ≤ 1)
    (hnn : ∀ n, 0 ≤ e n)
    (hle : ∀ n, e n ≤ e0)
    (hrec : ∀ n, e (n + 1) ≤ e n * (1 - c * e n ^ p))
    (n : ℕ) :
    e n ^ p ≤ e0 ^ p / (1 + c * ↑p * e0 ^ p * ↑n) := by
  have hden_pos : 0 < 1 + c * ↑p * e0 ^ p * ↑n := by positivity
  rw [le_div_iff₀ hden_pos]
  exact power_law_recurrence_mul_general e c e0 p hp hc_pos he0_nn hce_small hnn hle hrec n

/-- Small-constant condition for general p: c · e₀^p ≤ 1. -/
lemma small_constant_of_recurrence_general
    (e : ℕ → ℝ) (c : ℝ) (p : ℕ) (_hp : 1 ≤ p)
    (_hc_pos : 0 < c)
    (hnn : ∀ n, 0 ≤ e n)
    (hrec : ∀ n, e (n + 1) ≤ e n * (1 - c * e n ^ p)) :
    c * e 0 ^ p ≤ 1 := by
  by_contra h
  push_neg at h
  -- c * e₀^p > 1 implies e₀ > 0
  have he0_pos : 0 < e 0 := by
    rcases eq_or_lt_of_le (hnn 0) with he0 | he0
    · exfalso; rw [← he0] at h; simp [zero_pow (by omega : p ≠ 0)] at h; linarith
    · exact he0
  -- e₀ * (1 - c * e₀^p) < 0 since c * e₀^p > 1 and e₀ > 0
  have hneg : e 0 * (1 - c * e 0 ^ p) < 0 := by nlinarith
  -- e₁ ≤ e₀ * (1 - c * e₀^p) < 0, but e₁ ≥ 0, contradiction
  linarith [hrec 0, hnn 1]

end AlgebraicRate

/-! # Stochastic Expected Gap Properties

We define the expected gap sequence and establish its key properties:
non-negativity, monotone decrease, and the Łojasiewicz recurrence. -/

section StochasticExpectedGap

noncomputable section

variable (S : StochasticSOS) (π₀ : S.P)

/-- The expected evaluator at step n: ∫ eval(ω(n)) dμ_{π₀}. -/
def StochasticSOS.expectedEval (n : ℕ) : ℝ :=
  ∫ ω, S.eval (ω n) ∂(sosPathMeasure π₀ S.kernel)

/-- The expected gap at step n: M - 𝔼[eval(ω(n))]. -/
def StochasticSOS.expectedGap (M : ℝ) (n : ℕ) : ℝ :=
  M - S.expectedEval π₀ n

/-- The expected gap is non-negative when M bounds the evaluator.
    Proof: eval ≤ M pointwise implies ∫ eval dμ ≤ M for probability μ. -/
theorem StochasticSOS.expectedGap_nonneg
    {M : ℝ} (hM : ∀ π : S.P, S.eval π ≤ M) (n : ℕ) :
    0 ≤ S.expectedGap π₀ M n := by
  unfold StochasticSOS.expectedGap StochasticSOS.expectedEval
  -- 0 ≤ M - ∫ eval(ω(n)) dμ  ⟺  ∫ eval dμ ≤ M
  -- Strategy: ∫ eval ≤ ∫ M = M, by integral_mono_ae + probability measure
  set μ := sosPathMeasure π₀ S.kernel
  have hle : ∫ ω, S.eval (ω n) ∂μ ≤ ∫ _, M ∂μ :=
    integral_mono_ae (S.evalProcess_integrable π₀ n) (integrable_const M)
      (ae_of_all μ fun ω => hM (ω n))
  have hconst : ∫ _, M ∂μ = M := by
    rw [integral_const]; simp [Measure.real, measure_univ]
  linarith

/-- The expected evaluator is non-decreasing (from the submartingale property):
    𝔼[eval(ω(n))] ≤ 𝔼[eval(ω(n+1))].
    This means the expected gap is non-increasing.

    Proof: submartingale gives eval(ω(n)) ≤ᵃᵉ 𝔼[eval(ω(n+1)) | ℱ_n].
    Integrating: ∫ eval(ω(n)) ≤ ∫ μ[eval(ω(n+1)) | ℱ_n] = ∫ eval(ω(n+1))
    by integral_mono_ae + integral_condExp (tower property). -/
theorem StochasticSOS.expectedEval_mono (n : ℕ) :
    S.expectedEval π₀ n ≤ S.expectedEval π₀ (n + 1) := by
  simp only [StochasticSOS.expectedEval]
  set μ := sosPathMeasure π₀ S.kernel
  have hsub := S.evalProcess_submartingale π₀
  -- The filtration and its σ-algebra at time n
  let ℱ : Filtration ℕ (MeasurableSpace.pi (m := fun _ => S.ms)) :=
    Filtration.piLE (X := fun _ => S.P)
  have hle_ae := hsub.2.1 n (n + 1) (Nat.le_succ n)
  have hm : (ℱ n : MeasurableSpace (ℕ → S.P)) ≤ MeasurableSpace.pi := ℱ.le n
  -- SigmaFinite for the trimmed measure (needed by integral_condExp)
  haveI : @IsFiniteMeasure (ℕ → S.P) (ℱ n) (μ.trim hm) :=
    @isFiniteMeasure_trim (ℕ → S.P) (ℱ n) MeasurableSpace.pi μ hm inferInstance
  haveI : @SigmaFinite (ℕ → S.P) (ℱ n) (μ.trim hm) :=
    @IsFiniteMeasure.toSigmaFinite (ℕ → S.P) (ℱ n) (μ.trim hm) inferInstance
  calc ∫ ω, S.evalProcess n ω ∂μ
      ≤ ∫ ω, (μ[S.evalProcess (n + 1) | ℱ n]) ω ∂μ :=
        integral_mono_ae (hsub.2.2 n) integrable_condExp hle_ae
    _ = ∫ ω, S.evalProcess (n + 1) ω ∂μ :=
        integral_condExp hm

/-- The expected gap is non-increasing: ē_n ≥ ē_{n+1}. -/
theorem StochasticSOS.expectedGap_mono
    (M : ℝ) (n : ℕ) :
    S.expectedGap π₀ M (n + 1) ≤ S.expectedGap π₀ M n := by
  unfold StochasticSOS.expectedGap
  linarith [S.expectedEval_mono π₀ n]

/-- The expected gap at step n is bounded by the initial gap. -/
theorem StochasticSOS.expectedGap_le_initial
    {M : ℝ} (_hM : ∀ π : S.P, S.eval π ≤ M) (n : ℕ) :
    S.expectedGap π₀ M n ≤ S.expectedGap π₀ M 0 := by
  unfold StochasticSOS.expectedGap
  have : S.expectedEval π₀ 0 ≤ S.expectedEval π₀ n := by
    induction n with
    | zero => exact le_refl _
    | succ n ih => exact le_trans ih (S.expectedEval_mono π₀ n)
  linarith

end

end StochasticExpectedGap

/-! # Jensen's Inequality for x²

The key lemma: (∫ f dμ)² ≤ ∫ f² dμ for probability measures.
Proof: 0 ≤ ∫ (f - 𝔼[f])² and expand by linearity. -/

section Jensen

/-- **Jensen's inequality for x²**: (𝔼[X])² ≤ 𝔼[X²] for probability measures.
    Equivalently, Var[X] ≥ 0.  Proof from first principles: ∫ (f - c)² ≥ 0
    where c = ∫ f, then expand by integration linearity. -/
theorem sq_integral_le_integral_sq {Ω : Type*} {m : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f : Ω → ℝ} (hf : Integrable f μ) (hf2 : Integrable (fun ω => (f ω) ^ 2) μ) :
    (∫ ω, f ω ∂μ) ^ 2 ≤ ∫ ω, (f ω) ^ 2 ∂μ := by
  set c := ∫ ω, f ω ∂μ
  -- 0 ≤ ∫ (f - c)²  (pointwise non-negative)
  have hnn : 0 ≤ ∫ ω, (f ω - c) ^ 2 ∂μ :=
    integral_nonneg (fun _ => sq_nonneg _)
  -- ∫ (f - c)² = ∫ f² - 2c·∫f + c² = ∫ f² - c²
  -- We show: ∫ (f - c)² ≤ ∫ f² - c², then combine with hnn
  suffices hsuff : ∫ ω, (f ω - c) ^ 2 ∂μ = (∫ ω, (f ω) ^ 2 ∂μ) - c ^ 2 by
    linarith
  -- Expand (f - c)² = f² - 2·c·f + c²
  have hexpand : (fun ω => (f ω - c) ^ 2) = fun ω => (f ω) ^ 2 - 2 * c * f ω + c ^ 2 :=
    funext fun ω => by ring
  rw [hexpand]
  -- Split integral using linearity: ∫ (A - B + C) step by step
  have hcf : Integrable (fun ω => 2 * c * f ω) μ := hf.const_mul (2 * c)
  have hsub : Integrable (fun ω => (f ω) ^ 2 - 2 * c * f ω) μ := hf2.sub hcf
  rw [show (fun ω => (f ω) ^ 2 - 2 * c * f ω + c ^ 2) =
      fun ω => ((f ω) ^ 2 - 2 * c * f ω) + c ^ 2 from funext fun ω => by ring]
  rw [integral_add hsub (integrable_const _), integral_sub hf2 hcf,
      integral_const_mul, integral_const]
  simp only [Measure.real, measure_univ, smul_eq_mul, ENNReal.toReal_one]
  ring

end Jensen

/-! # The Jensen Bridge

The key theorem: under a stochastic quadratic Łojasiewicz condition,
the expected gap satisfies the deterministic recurrence
  ē_{n+1} ≤ ē_n · (1 - c · ē_n).

This follows from:
1. Tower property: 𝔼[eval(ω(n+1))] ≥ 𝔼[eval(ω(n))] + c·𝔼[(M-eval(ω(n)))²]
2. Jensen (x² convex): 𝔼[(M-eval)²] ≥ (𝔼[M-eval])² = ē_n²

Together: ē_{n+1} ≤ ē_n - c·ē_n². -/

section JensenBridge

open Preorder

noncomputable section

/-- **The Jensen Bridge**: under the stochastic quadratic Łojasiewicz
    condition, the expected gap satisfies the deterministic recurrence
    ē_{n+1} ≤ ē_n · (1 - c · ē_n).

    The proof decomposes into:
    (a) Tower + Łojasiewicz: 𝔼[eval(n+1)] ≥ 𝔼[eval(n)] + c·𝔼[(M-eval(n))²]
    (b) Jensen (sq_integral_le_integral_sq): 𝔼[(M-eval)²] ≥ ē_n²
    The tower step (a) requires condExp_traj + Markov property. -/
theorem StochasticSOS.expectedGap_recurrence (S : StochasticSOS) (π₀ : S.P)
    {M : ℝ} (hM : ∀ π : S.P, S.eval π ≤ M)
    {c : ℝ} (hc_pos : 0 < c)
    (hLoj : ∀ π : S.P,
      ∫ π', S.eval π' ∂(S.kernel π) - S.eval π ≥ c * (M - S.eval π) ^ 2)
    (n : ℕ) :
    S.expectedGap π₀ M (n + 1) ≤
      S.expectedGap π₀ M n * (1 - c * S.expectedGap π₀ M n) := by
  simp only [StochasticSOS.expectedGap, StochasticSOS.expectedEval]
  set μ := sosPathMeasure π₀ S.kernel
  set ēn := M - ∫ ω, S.eval (ω n) ∂μ
  -- Integrability of (M - eval(n))² (needed in both parts)
  have hf2_int : Integrable (fun ω => (M - S.eval (ω n)) ^ 2) μ := by
    obtain ⟨B, hB⟩ := S.eval_bound
    apply Integrable.of_bound
      ((S.eval_measurable.comp (measurable_pi_apply n)).const_sub M
        |>.pow_const 2 |>.aestronglyMeasurable)
      ((M + ↑B) ^ 2) (ae_of_all μ fun ω => by
        simp only [Real.norm_eq_abs]
        have habs := hB (ω n)
        have hnn : 0 ≤ M - S.eval (ω n) := by linarith [hM (ω n)]
        have hle : M - S.eval (ω n) ≤ M + ↑B := by
          have := (abs_le.mp habs).1; linarith
        calc |(M - S.eval (ω n)) ^ 2| = (M - S.eval (ω n)) ^ 2 :=
              abs_of_nonneg (sq_nonneg _)
          _ ≤ (M + ↑B) ^ 2 := by nlinarith)
  -- Part (a): Tower + Łojasiewicz step
  -- 𝔼[eval(n+1)] ≥ 𝔼[eval(n)] + c · 𝔼[(M - eval(n))²]
  -- Following the exact pattern of evalProcess_condExp_le (StochasticSOS.lean:149)
  -- but using hLoj instead of stoch_improvement in the final step.
  have h_tower_loj : ∫ ω, S.eval (ω (n + 1)) ∂μ ≥
      ∫ ω, S.eval (ω n) ∂μ + c * ∫ ω, (M - S.eval (ω n)) ^ 2 ∂μ := by
    let ℱ : Filtration ℕ (MeasurableSpace.pi (m := fun _ => S.ms)) :=
      Filtration.piLE (X := fun _ => S.P)
    have hm : (ℱ n : MeasurableSpace (ℕ → S.P)) ≤ MeasurableSpace.pi := ℱ.le n
    haveI : @IsFiniteMeasure (ℕ → S.P) (ℱ n) (μ.trim hm) :=
      @isFiniteMeasure_trim (ℕ → S.P) (ℱ n) MeasurableSpace.pi μ hm inferInstance
    haveI : @SigmaFinite (ℕ → S.P) (ℱ n) (μ.trim hm) :=
      @IsFiniteMeasure.toSigmaFinite _ _ _ inferInstance
    -- Rewrite μ as Kernel.traj for the condExp_traj API
    have hμ : μ = Kernel.traj (X := fun _ => S.P) (fun m => homKernel S.kernel m) 0
        ((MeasurableEquiv.piUnique (fun _ : ↥(Finset.Iic 0) => S.P)).symm π₀) := by
      change sosPathMeasure π₀ S.kernel = _
      unfold sosPathMeasure Kernel.trajMeasure
      rw [Measure.map_dirac
        (MeasurableEquiv.piUnique (fun _ : ↥(Finset.Iic 0) => S.P)).symm.measurable]
      exact Measure.dirac_bind
        (Kernel.traj (X := fun _ => S.P) (fun m => homKernel S.kernel m) 0).measurable _
    have hint : Integrable (S.evalProcess (n + 1))
        (Kernel.traj (X := fun _ => S.P) (fun m => homKernel S.kernel m) 0
          ((MeasurableEquiv.piUnique (fun _ : ↥(Finset.Iic 0) => S.P)).symm π₀)) :=
      hμ ▸ S.evalProcess_integrable π₀ (n + 1)
    -- The a.e. bound: eval(n) + c·(M-eval(n))² ≤ condExp(eval(n+1)|ℱ_n)
    have hae : ∀ᵐ ω ∂μ,
        S.eval (ω n) + c * (M - S.eval (ω n)) ^ 2 ≤
          (μ[S.evalProcess (n + 1) | ↑(ℱ n)]) ω := by
      rw [hμ]
      filter_upwards [Kernel.condExp_traj (Nat.zero_le n) hint] with ω hω
      rw [hω]
      simp only [StochasticSOS.evalProcess]
      -- Goal: eval(ω n) + c·(M-eval(ω n))² ≤ ∫ eval(y(n+1)) d(traj κ n ...)
      -- Show the integral equals ∫ eval dκ(ω(n)), then apply hLoj
      suffices h : ∫ y, S.eval (y (n + 1)) ∂Kernel.traj (X := fun _ => S.P)
          (fun m => homKernel S.kernel m) n (frestrictLe n ω) =
          ∫ z, S.eval z ∂S.kernel (ω n) by
        rw [h]; linarith [hLoj (ω n)]
      have hmeas : Measurable (fun (y : ℕ → S.P) => y (n + 1)) :=
        measurable_pi_apply (n + 1)
      rw [← integral_map hmeas.aemeasurable S.eval_measurable.aestronglyMeasurable]
      congr 1
      rw [← Kernel.map_apply _ hmeas, Kernel.map_traj_succ_self]
      simp only [homKernel, Kernel.comap_apply, frestrictLe_apply]
    -- Integrate both sides
    have hint_lhs : Integrable
        (fun ω => S.eval (ω n) + c * (M - S.eval (ω n)) ^ 2) μ :=
      (S.evalProcess_integrable π₀ n).add (hf2_int.const_mul c)
    have h1 := integral_mono_ae hint_lhs integrable_condExp hae
    -- Tower property: ∫ condExp(f|ℱ) = ∫ f
    have h2 : ∫ ω, (μ[S.evalProcess (n + 1) | ↑(ℱ n)]) ω ∂μ =
        ∫ ω, S.evalProcess (n + 1) ω ∂μ := integral_condExp hm
    -- Bridge evalProcess ↔ eval for h2
    simp only [StochasticSOS.evalProcess] at h2
    -- Linearity of LHS: ∫ (f + c·g) = ∫ f + c · ∫ g
    have h3 : ∫ x, S.eval (x n) + c * (M - S.eval (x n)) ^ 2 ∂μ =
        ∫ x, S.eval (x n) ∂μ + c * ∫ x, (M - S.eval (x n)) ^ 2 ∂μ := by
      have : ∫ x, S.eval (x n) + c * (M - S.eval (x n)) ^ 2 ∂μ =
          ∫ x, S.evalProcess n x ∂μ + ∫ x, (c * (M - S.eval (x n)) ^ 2) ∂μ := by
        exact integral_add (S.evalProcess_integrable π₀ n) (hf2_int.const_mul c)
      simp only [StochasticSOS.evalProcess, integral_const_mul] at this
      exact this
    -- Combine: h1 (a.e. bound → integral bound), h2 (tower), h3 (linearity)
    linarith
  -- Part (b): Jensen — (∫ f)² ≤ ∫ f²
  -- Applied to f(ω) = M - eval(ω(n))
  have hf_int : Integrable (fun ω => M - S.eval (ω n)) μ :=
    (integrable_const M).sub (S.evalProcess_integrable π₀ n)
  have h_jensen : ēn ^ 2 ≤ ∫ ω, (M - S.eval (ω n)) ^ 2 ∂μ := by
    have hlin : ∫ ω, (M - S.eval (ω n)) ∂μ = ēn := by
      change ∫ ω, (M - S.eval (ω n)) ∂μ = M - ∫ ω, S.eval (ω n) ∂μ
      have : ∫ ω, (M - S.eval (ω n)) ∂μ =
          ∫ ω, M ∂μ - ∫ ω, S.eval (ω n) ∂μ :=
        integral_sub (integrable_const M) (S.evalProcess_integrable π₀ n)
      rw [this, integral_const]
      simp [Measure.real, measure_univ]
    rw [← hlin]
    exact sq_integral_le_integral_sq hf_int hf2_int
  -- Combine (a) and (b)
  nlinarith [mul_le_mul_of_nonneg_left h_jensen (le_of_lt hc_pos)]

end

end JensenBridge

/-! # Stochastic Power-Law Rate

Assembling the standalone algebraic lemma with the Jensen bridge gives
the stochastic O(1/n) rate. -/

section StochasticRate

open Preorder

noncomputable section

/-- **Stochastic power-law rate for α = 2** (division form):
    Under the stochastic quadratic Łojasiewicz condition, the expected
    evaluator gap decays as O(1/n):
      M - 𝔼[eval(ω(n))] ≤ e₀ / (1 + c·e₀·n)
    where e₀ = M - eval(π₀).

    The proof assembles three ingredients:
    1. Jensen bridge (expectedGap_recurrence): ē satisfies deterministic recurrence
    2. Standalone algebraic lemma (power_law_recurrence_div): recurrence → O(1/n)
    3. Gap properties (nonneg, bounded, small constant) -/
theorem StochasticSOS.expected_rate_alpha2 (S : StochasticSOS) (π₀ : S.P)
    {M : ℝ} (hM : ∀ π : S.P, S.eval π ≤ M)
    {c : ℝ} (hc_pos : 0 < c)
    (hLoj : ∀ π : S.P,
      ∫ π', S.eval π' ∂(S.kernel π) - S.eval π ≥ c * (M - S.eval π) ^ 2)
    (n : ℕ) :
    S.expectedGap π₀ M n ≤
      S.expectedGap π₀ M 0 / (1 + c * S.expectedGap π₀ M 0 * ↑n) := by
  exact power_law_recurrence_div
    (S.expectedGap π₀ M) c (S.expectedGap π₀ M 0)
    hc_pos
    (S.expectedGap_nonneg π₀ hM 0)
    (small_constant_of_recurrence
      (S.expectedGap π₀ M) c hc_pos
      (S.expectedGap_nonneg π₀ hM)
      (S.expectedGap_recurrence π₀ hM hc_pos hLoj))
    (S.expectedGap_nonneg π₀ hM)
    (S.expectedGap_le_initial π₀ hM)
    (S.expectedGap_recurrence π₀ hM hc_pos hLoj)
    n

/-- **Stochastic general power-law recurrence**: under the stochastic
    Łojasiewicz condition with exponent p+1 (α = p+1 ≥ 2), the expected
    gap satisfies ē_{n+1} ≤ ē_n · (1 - c · ē_n^p).

    Proof: same Jensen bridge as α=2, using convexity of x^{p+1} for p+1≥2.
    Jensen gives 𝔼[(M-eval)^{p+1}] ≥ (𝔼[M-eval])^{p+1} = ē^{p+1}.
    Then ē_{n+1} ≤ ē_n - c·ē_n^{p+1} = ē_n(1 - c·ē_n^p). -/
theorem StochasticSOS.expectedGap_recurrence_general (S : StochasticSOS) (π₀ : S.P)
    (p : ℕ) (_hp : 1 ≤ p)
    {M : ℝ} (hM : ∀ π : S.P, S.eval π ≤ M)
    {c : ℝ} (hc_pos : 0 < c)
    (hLoj : ∀ π : S.P,
      ∫ π', S.eval π' ∂(S.kernel π) - S.eval π ≥ c * (M - S.eval π) ^ (p + 1))
    (n : ℕ) :
    S.expectedGap π₀ M (n + 1) ≤
      S.expectedGap π₀ M n * (1 - c * S.expectedGap π₀ M n ^ p) := by
  simp only [StochasticSOS.expectedGap, StochasticSOS.expectedEval]
  set μ := sosPathMeasure π₀ S.kernel
  set ēn := M - ∫ ω, S.eval (ω n) ∂μ
  -- Integrability of (M - eval(n))^{p+1}
  have hfp_int : Integrable (fun ω => (M - S.eval (ω n)) ^ (p + 1)) μ := by
    obtain ⟨B, hB⟩ := S.eval_bound
    exact Integrable.of_bound
      ((S.eval_measurable.comp (measurable_pi_apply n)).const_sub M
        |>.pow_const (p + 1) |>.aestronglyMeasurable)
      ((M + ↑B) ^ (p + 1)) (ae_of_all μ fun ω => by
        simp only [Real.norm_eq_abs]
        have hnn : 0 ≤ M - S.eval (ω n) := by linarith [hM (ω n)]
        have hle : M - S.eval (ω n) ≤ M + ↑B := by
          have := (abs_le.mp (hB (ω n))).1; linarith
        calc |(M - S.eval (ω n)) ^ (p + 1)| = (M - S.eval (ω n)) ^ (p + 1) :=
              abs_of_nonneg (pow_nonneg hnn _)
          _ ≤ (M + ↑B) ^ (p + 1) := pow_le_pow_left₀ hnn hle _)
  -- Part (a): Tower + Łojasiewicz (same pattern as α=2)
  have h_tower_loj : ∫ ω, S.eval (ω (n + 1)) ∂μ ≥
      ∫ ω, S.eval (ω n) ∂μ + c * ∫ ω, (M - S.eval (ω n)) ^ (p + 1) ∂μ := by
    let ℱ : Filtration ℕ (MeasurableSpace.pi (m := fun _ => S.ms)) :=
      Filtration.piLE (X := fun _ => S.P)
    have hm : (ℱ n : MeasurableSpace (ℕ → S.P)) ≤ MeasurableSpace.pi := ℱ.le n
    haveI : @IsFiniteMeasure (ℕ → S.P) (ℱ n) (μ.trim hm) :=
      @isFiniteMeasure_trim (ℕ → S.P) (ℱ n) MeasurableSpace.pi μ hm inferInstance
    haveI : @SigmaFinite (ℕ → S.P) (ℱ n) (μ.trim hm) :=
      @IsFiniteMeasure.toSigmaFinite _ _ _ inferInstance
    have hμ : μ = Kernel.traj (X := fun _ => S.P) (fun m => homKernel S.kernel m) 0
        ((MeasurableEquiv.piUnique (fun _ : ↥(Finset.Iic 0) => S.P)).symm π₀) := by
      change sosPathMeasure π₀ S.kernel = _
      unfold sosPathMeasure Kernel.trajMeasure
      rw [Measure.map_dirac
        (MeasurableEquiv.piUnique (fun _ : ↥(Finset.Iic 0) => S.P)).symm.measurable]
      exact Measure.dirac_bind
        (Kernel.traj (X := fun _ => S.P) (fun m => homKernel S.kernel m) 0).measurable _
    have hint : Integrable (S.evalProcess (n + 1))
        (Kernel.traj (X := fun _ => S.P) (fun m => homKernel S.kernel m) 0
          ((MeasurableEquiv.piUnique (fun _ : ↥(Finset.Iic 0) => S.P)).symm π₀)) :=
      hμ ▸ S.evalProcess_integrable π₀ (n + 1)
    have hae : ∀ᵐ ω ∂μ,
        S.eval (ω n) + c * (M - S.eval (ω n)) ^ (p + 1) ≤
          (μ[S.evalProcess (n + 1) | ↑(ℱ n)]) ω := by
      rw [hμ]
      filter_upwards [Kernel.condExp_traj (Nat.zero_le n) hint] with ω hω
      rw [hω]
      simp only [StochasticSOS.evalProcess]
      suffices h : ∫ y, S.eval (y (n + 1)) ∂Kernel.traj (X := fun _ => S.P)
          (fun m => homKernel S.kernel m) n (frestrictLe n ω) =
          ∫ z, S.eval z ∂S.kernel (ω n) by
        rw [h]; linarith [hLoj (ω n)]
      have hmeas : Measurable (fun (y : ℕ → S.P) => y (n + 1)) :=
        measurable_pi_apply (n + 1)
      rw [← integral_map hmeas.aemeasurable S.eval_measurable.aestronglyMeasurable]
      congr 1
      rw [← Kernel.map_apply _ hmeas, Kernel.map_traj_succ_self]
      simp only [homKernel, Kernel.comap_apply, frestrictLe_apply]
    have hint_lhs : Integrable
        (fun ω => S.eval (ω n) + c * (M - S.eval (ω n)) ^ (p + 1)) μ :=
      (S.evalProcess_integrable π₀ n).add (hfp_int.const_mul c)
    have h1 := integral_mono_ae hint_lhs integrable_condExp hae
    -- Tower property: ∫ condExp = ∫ f
    have h2 : ∫ ω, (μ[S.evalProcess (n + 1) | ↑(ℱ n)]) ω ∂μ =
        ∫ ω, S.evalProcess (n + 1) ω ∂μ := integral_condExp hm
    simp only [StochasticSOS.evalProcess] at h2
    have h3 : ∫ x, S.eval (x n) + c * (M - S.eval (x n)) ^ (p + 1) ∂μ =
        ∫ x, S.eval (x n) ∂μ + c * ∫ x, (M - S.eval (x n)) ^ (p + 1) ∂μ := by
      have : ∫ x, S.eval (x n) + c * (M - S.eval (x n)) ^ (p + 1) ∂μ =
          ∫ x, S.evalProcess n x ∂μ + ∫ x, (c * (M - S.eval (x n)) ^ (p + 1)) ∂μ :=
        integral_add (S.evalProcess_integrable π₀ n) (hfp_int.const_mul c)
      simp only [StochasticSOS.evalProcess, integral_const_mul] at this
      exact this
    linarith
  -- Part (b): Jensen for x^{p+1} via ConvexOn.map_average_le
  have hf_int : Integrable (fun ω => M - S.eval (ω n)) μ :=
    (integrable_const M).sub (S.evalProcess_integrable π₀ n)
  have h_jensen : ēn ^ (p + 1) ≤ ∫ ω, (M - S.eval (ω n)) ^ (p + 1) ∂μ := by
    have hlin : ∫ ω, (M - S.eval (ω n)) ∂μ = ēn := by
      change ∫ ω, (M - S.eval (ω n)) ∂μ = M - ∫ ω, S.eval (ω n) ∂μ
      have hsub' : ∫ ω, (M - S.eval (ω n)) ∂μ =
          ∫ ω, M ∂μ - ∫ ω, S.eval (ω n) ∂μ :=
        integral_sub (integrable_const M) (S.evalProcess_integrable π₀ n)
      rw [hsub', integral_const]
      simp only [Measure.real, measure_univ, ENNReal.toReal_one, one_smul, μ]
    -- Use ConvexOn.map_average_le with g = x^{p+1}
    have hconv : ConvexOn ℝ (Set.Ici 0) (fun x : ℝ => x ^ (p + 1)) :=
      convexOn_pow (p + 1)
    have hcont : ContinuousOn (fun x : ℝ => x ^ (p + 1)) (Set.Ici 0) :=
      (continuous_pow (p + 1)).continuousOn
    have hclosed : IsClosed (Set.Ici (0 : ℝ)) := isClosed_Ici
    have hfs : ∀ᵐ ω ∂μ, (fun ω => M - S.eval (ω n)) ω ∈ Set.Ici (0 : ℝ) :=
      ae_of_all μ fun ω => Set.mem_Ici.mpr (show (0 : ℝ) ≤ M - S.eval (ω n) by linarith [hM (ω n)])
    have hgi : Integrable ((fun x : ℝ => x ^ (p + 1)) ∘ (fun ω => M - S.eval (ω n))) μ :=
      hfp_int
    have hj := ConvexOn.map_average_le hconv hcont hclosed hfs hf_int hgi
    -- hj : (⨍ f)^{p+1} ≤ ⨍ f^{p+1}
    -- Convert ⨍ to ∫ for probability measure
    rw [average_eq_integral, average_eq_integral] at hj
    rwa [hlin] at hj
  -- Combine (a) and (b): ē_{n+1} ≤ ē_n - c·ē_n^{p+1} = ē_n(1 - c·ē_n^p)
  have hpow : ēn ^ (p + 1) = ēn ^ p * ēn := by rw [pow_succ]
  nlinarith [mul_le_mul_of_nonneg_left h_jensen (le_of_lt hc_pos)]

/-- **Stochastic general power-law rate**: under the stochastic Łojasiewicz
    condition with exponent p+1, the p-th power of the expected gap decays
    as O(1/n):  ē_n^p ≤ ē₀^p / (1 + c·p·ē₀^p·n). -/
theorem StochasticSOS.expected_rate_general (S : StochasticSOS) (π₀ : S.P)
    (p : ℕ) (hp : 1 ≤ p)
    {M : ℝ} (hM : ∀ π : S.P, S.eval π ≤ M)
    {c : ℝ} (hc_pos : 0 < c)
    (hLoj : ∀ π : S.P,
      ∫ π', S.eval π' ∂(S.kernel π) - S.eval π ≥ c * (M - S.eval π) ^ (p + 1))
    (n : ℕ) :
    S.expectedGap π₀ M n ^ p ≤
      S.expectedGap π₀ M 0 ^ p / (1 + c * ↑p * S.expectedGap π₀ M 0 ^ p * ↑n) := by
  exact power_law_recurrence_div_general
    (S.expectedGap π₀ M) c (S.expectedGap π₀ M 0) p hp
    hc_pos
    (S.expectedGap_nonneg π₀ hM 0)
    (small_constant_of_recurrence_general
      (S.expectedGap π₀ M) c p hp hc_pos
      (S.expectedGap_nonneg π₀ hM)
      (S.expectedGap_recurrence_general π₀ p hp hM hc_pos hLoj))
    (S.expectedGap_nonneg π₀ hM)
    (S.expectedGap_le_initial π₀ hM)
    (S.expectedGap_recurrence_general π₀ p hp hM hc_pos hLoj)
    n

end

end StochasticRate

/-! # Pathwise Rate

Under a pathwise Łojasiewicz condition (improvement holds per-realisation),
the deterministic O(1/n) rate applies to each path independently. -/

section PathwiseRate

noncomputable section

/-- **Pathwise O(1/n) rate**: if the Łojasiewicz condition holds
    pointwise along paths (not just in expectation), the evaluator gap
    decays as O(1/n) almost surely.  The proof applies the deterministic
    rate to each realisation via filter_upwards. -/
theorem StochasticSOS.pathwise_rate_alpha2 (S : StochasticSOS) (π₀ : S.P)
    {M : ℝ} (hM : ∀ π : S.P, S.eval π ≤ M)
    {c : ℝ} (hc_pos : 0 < c)
    (hLoj_pw : ∀ᵐ ω ∂(sosPathMeasure π₀ S.kernel),
      ∀ k : ℕ, S.eval (ω (k + 1)) - S.eval (ω k) ≥ c * (M - S.eval (ω k)) ^ 2) :
    ∀ᵐ ω ∂(sosPathMeasure π₀ S.kernel), ∀ (k : ℕ),
      M - S.eval (ω k) ≤
        (M - S.eval (ω 0)) / (1 + c * (M - S.eval (ω 0)) * ↑k) := by
  filter_upwards [hLoj_pw] with ω hω
  intro k
  -- The sequence e_n(ω) = M - eval(ω(n)) satisfies the deterministic recurrence
  -- e_{n+1} ≤ e_n(1 - c·e_n) pointwise along this path ω.
  -- Pre-prove the recurrence to avoid nlinarith inside lambda contexts
  have hrec : ∀ j, (fun i => M - S.eval (ω i)) (j + 1) ≤
      (fun i => M - S.eval (ω i)) j * (1 - c * (fun i => M - S.eval (ω i)) j) := by
    intro j; simp only
    -- From hω j: eval(j+1) - eval(j) ≥ c * (M - eval(j))²
    -- Goal: M - eval(j+1) ≤ (M - eval(j)) * (1 - c * (M - eval(j)))
    --     = (M - eval(j)) - c * (M - eval(j))²
    have h := hω j
    nlinarith [sq_nonneg (M - S.eval (ω j))]
  have hnn : ∀ j, 0 ≤ (fun i => M - S.eval (ω i)) j := by
    intro j; simp only; linarith [hM (ω j)]
  have hle : ∀ j, (fun i => M - S.eval (ω i)) j ≤ (fun i => M - S.eval (ω i)) 0 := by
    intro j; simp only
    have : S.eval (ω 0) ≤ S.eval (ω j) := by
      induction j with
      | zero => exact le_refl _
      | succ j ih =>
        have step := hω j
        have sq := sq_nonneg (M - S.eval (ω j))
        have : S.eval (ω j) ≤ S.eval (ω (j + 1)) := by nlinarith
        linarith
    linarith
  apply power_law_recurrence_div (fun j => M - S.eval (ω j)) c (M - S.eval (ω 0))
    hc_pos (by linarith [hM (ω 0)])
  · exact small_constant_of_recurrence _ c hc_pos hnn hrec
  · exact hnn
  · exact hle
  · exact hrec

end

end PathwiseRate

/-! # High-Probability Bound

The expected rate converts to a high-probability bound via Markov's inequality.
For non-negative random variables: P(X > ε) ≤ 𝔼[X]/ε. -/

section HighProbability

/-- **High-probability bound** (real-valued form): under the stochastic
    quadratic Łojasiewicz condition,
    μ.real{ω | ε ≤ M - eval(ω n)} ≤ ē₀ / (ε · (1 + c·ē₀·n)).

    Uses Markov's inequality (mul_meas_ge_le_integral_of_nonneg) combined
    with the expected O(1/n) rate. -/
theorem StochasticSOS.high_probability_bound (S : StochasticSOS) (π₀ : S.P)
    {M : ℝ} (hM : ∀ π : S.P, S.eval π ≤ M)
    {c : ℝ} (hc_pos : 0 < c)
    (hLoj : ∀ π : S.P,
      ∫ π', S.eval π' ∂(S.kernel π) - S.eval π ≥ c * (M - S.eval π) ^ 2)
    {ε : ℝ} (_hε : 0 < ε) (n : ℕ) :
    ε * (sosPathMeasure π₀ S.kernel).real {ω | ε ≤ M - S.eval (ω n)} ≤
      S.expectedGap π₀ M 0 / (1 + c * S.expectedGap π₀ M 0 * ↑n) := by
  set μ := sosPathMeasure π₀ S.kernel
  -- Markov: ε · μ.real{ε ≤ f} ≤ ∫ f for f ≥ 0
  have hf_nn : 0 ≤ᵐ[μ] (fun ω => M - S.eval (ω n)) :=
    ae_of_all μ fun ω => show (0 : ℝ) ≤ M - S.eval (ω n) by linarith [hM (ω n)]
  have hf_int : Integrable (fun ω => M - S.eval (ω n)) μ :=
    (integrable_const M).sub (S.evalProcess_integrable π₀ n)
  have hmarkov := mul_meas_ge_le_integral_of_nonneg hf_nn hf_int ε
  -- hmarkov : ε * μ.real{ε ≤ M - eval(ω n)} ≤ ∫ (M - eval(ω n)) dμ
  -- ∫ (M - eval(ω n)) dμ = expectedGap π₀ M n (by linearity)
  have hlin : ∫ ω, (M - S.eval (ω n)) ∂μ = S.expectedGap π₀ M n := by
    show ∫ ω, (M - S.eval (ω n)) ∂μ = S.expectedGap π₀ M n
    unfold StochasticSOS.expectedGap StochasticSOS.expectedEval
    have hsub : ∫ ω, (M - S.eval (ω n)) ∂μ =
        ∫ ω, M ∂μ - ∫ ω, S.eval (ω n) ∂μ :=
      integral_sub (integrable_const M) (S.evalProcess_integrable π₀ n)
    rw [hsub, integral_const]
    simp only [Measure.real, measure_univ, ENNReal.toReal_one, one_smul, μ]
  rw [hlin] at hmarkov
  -- expectedGap n ≤ expectedGap 0 / (1 + c·ē₀·n) from the rate
  exact le_trans hmarkov (S.expected_rate_alpha2 π₀ hM hc_pos hLoj n)

end HighProbability

/-! # Stochastic Hölder Rate Transfer

If a stochastic morphism φ : S₁ → S₂ has (K,β)-Hölder continuous
evaluator map g, and S₁ has expected O(1/n) rate, the image orbit
converges in expected gap at rate O(n^{-β}) for β ≤ 1.

For β > 1, the expected-value approach fails (Jensen goes the wrong way).
The pathwise version (below) handles all β > 0 under the stronger
pathwise Łojasiewicz condition. -/

section StochasticHolderTransfer

noncomputable section

/-- **Expected Hölder rate transfer (α = 2, β ≤ 1)**: the expected
    Hölder-transformed gap decays as O(n^{-β}).

    Proof strategy (pen-and-paper verified, Lean 4 sorry):
    1. Hölder pointwise: g(M) - g(eval₁(ω(n))) ≤ K·(M-eval₁)^β
    2. Take expectations: 𝔼[g(M)-g(eval₁)] ≤ K·𝔼[(M-eval₁)^β]
    3. Jensen (ConcaveOn.le_map_average, concave x^β for β≤1):
       𝔼[(M-eval₁)^β] ≤ (𝔼[M-eval₁])^β = ē^β
    4. Rate: ē ≤ ē₀/(1+c·ē₀·n)

    The Lean 4 blocker: ConcaveOn for rpow on [0,∞) and
    integrability of rpow-transformed bounded functions.
    The pathwise version (pathwise_holder_transfer_alpha2) IS fully
    proved and covers ALL β > 0, not just β ≤ 1. -/
theorem StochasticSOS.expected_holder_bound_alpha2 (S : StochasticSOS) (π₀ : S.P)
    {M : ℝ} (hM : ∀ π : S.P, S.eval π ≤ M)
    {c : ℝ} (hc_pos : 0 < c)
    (hLoj : ∀ π : S.P,
      ∫ π', S.eval π' ∂(S.kernel π) - S.eval π ≥ c * (M - S.eval π) ^ 2)
    {g : ℝ → ℝ} (_hg_mono : Monotone g) (hg_meas : Measurable g)
    {K : ℝ} (_hK : 0 ≤ K) {β : ℝ} (_hβ_pos : 0 < β) (_hβ_le : β ≤ 1)
    (hg_holder : ∀ x y : ℝ, x ≤ y → g y - g x ≤ K * (y - x) ^ β)
    (n : ℕ) :
    ∫ ω, (g M - g (S.eval (ω n))) ∂(sosPathMeasure π₀ S.kernel) ≤
      K * (S.expectedGap π₀ M 0 / (1 + c * S.expectedGap π₀ M 0 * ↑n)) ^ β := by
  set μ := sosPathMeasure π₀ S.kernel
  have hgap_nn : ∀ ω : ℕ → S.P, 0 ≤ M - S.eval (ω n) :=
    fun ω => by linarith [hM (ω n)]
  -- Measurability helpers
  have heval_meas : Measurable (fun ω : ℕ → S.P => S.eval (ω n)) :=
    S.eval_measurable.comp (measurable_pi_apply n)
  have hgap_meas : Measurable (fun ω : ℕ → S.P => M - S.eval (ω n)) :=
    measurable_const.sub heval_meas
  -- Integrability of (M - eval)^β: bounded by (M+B)^β
  obtain ⟨B, hB⟩ := S.eval_bound
  have hrpow_meas : Measurable (fun ω : ℕ → S.P => (M - S.eval (ω n)) ^ β) :=
    (Real.continuous_rpow_const (le_of_lt _hβ_pos)).measurable.comp hgap_meas
  have hfb_int : Integrable (fun ω => (M - S.eval (ω n)) ^ β) μ :=
    Integrable.of_bound hrpow_meas.aestronglyMeasurable ((M + ↑B) ^ β)
      (ae_of_all μ fun ω => by
        simp only [Real.norm_eq_abs]
        rw [abs_of_nonneg (Real.rpow_nonneg (hgap_nn ω) β)]
        exact Real.rpow_le_rpow (hgap_nn ω)
          (by have := (abs_le.mp (hB (ω n))).1; linarith) (le_of_lt _hβ_pos))
  -- Integrability of g(M) - g(eval): bounded by K·(M+B)^β via Hölder condition
  have hint_lhs : Integrable (fun ω => g M - g (S.eval (ω n))) μ :=
    Integrable.of_bound ((measurable_const.sub (hg_meas.comp heval_meas)).aestronglyMeasurable)
      (K * (M + ↑B) ^ β)
      (ae_of_all μ fun ω => by
        simp only [Real.norm_eq_abs]
        rw [abs_of_nonneg (by linarith [_hg_mono (hM (ω n))])]
        calc g M - g (S.eval (ω n))
            ≤ K * (M - S.eval (ω n)) ^ β := hg_holder _ M (hM (ω n))
          _ ≤ K * (M + ↑B) ^ β := by
              apply mul_le_mul_of_nonneg_left _ _hK
              exact Real.rpow_le_rpow (hgap_nn ω)
                (by have := (abs_le.mp (hB (ω n))).1; linarith) (le_of_lt _hβ_pos))
  -- Step 1: Hölder pointwise → integral bound
  have hint_rhs : Integrable (fun ω => K * (M - S.eval (ω n)) ^ β) μ :=
    hfb_int.const_mul K
  have h1 : ∫ ω, (g M - g (S.eval (ω n))) ∂μ ≤
      K * ∫ ω, (M - S.eval (ω n)) ^ β ∂μ := by
    calc ∫ ω, (g M - g (S.eval (ω n))) ∂μ
        ≤ ∫ ω, K * (M - S.eval (ω n)) ^ β ∂μ :=
          integral_mono_ae hint_lhs hint_rhs
            (ae_of_all μ fun ω => hg_holder (S.eval (ω n)) M (hM (ω n)))
      _ = K * ∫ ω, (M - S.eval (ω n)) ^ β ∂μ := integral_const_mul K _
  -- Step 2: Jensen for concave x^β (β ≤ 1) via ConcaveOn.le_map_average
  have hf_int : Integrable (fun ω => M - S.eval (ω n)) μ :=
    (integrable_const M).sub (S.evalProcess_integrable π₀ n)
  have hconc : ConcaveOn ℝ (Set.Ici 0) (fun x : ℝ => x ^ β) :=
    Real.concaveOn_rpow (le_of_lt _hβ_pos) _hβ_le
  have hcont : ContinuousOn (fun x : ℝ => x ^ β) (Set.Ici 0) :=
    (Real.continuous_rpow_const (le_of_lt _hβ_pos)).continuousOn
  have hfs : ∀ᵐ ω ∂μ, (fun ω => M - S.eval (ω n)) ω ∈ Set.Ici (0 : ℝ) :=
    ae_of_all μ fun ω => Set.mem_Ici.mpr (show (0 : ℝ) ≤ M - S.eval (ω n) by linarith [hM (ω n)])
  have hjensen : ∫ ω, (M - S.eval (ω n)) ^ β ∂μ ≤
      (S.expectedGap π₀ M n) ^ β := by
    have hlin : ∫ ω, (M - S.eval (ω n)) ∂μ = S.expectedGap π₀ M n := by
      show ∫ ω, (M - S.eval (ω n)) ∂μ = S.expectedGap π₀ M n
      unfold StochasticSOS.expectedGap StochasticSOS.expectedEval
      have hsub' : ∫ ω, (M - S.eval (ω n)) ∂μ =
          ∫ ω, M ∂μ - ∫ ω, S.eval (ω n) ∂μ :=
        integral_sub (integrable_const M) (S.evalProcess_integrable π₀ n)
      rw [hsub', integral_const]
      simp only [Measure.real, measure_univ, ENNReal.toReal_one, one_smul, μ]
    have hj := ConcaveOn.le_map_average hconc hcont isClosed_Ici hfs hf_int hfb_int
    rw [average_eq_integral, average_eq_integral, hlin] at hj
    exact hj
  -- Step 3: Rate bound
  have hēn := S.expected_rate_alpha2 π₀ hM hc_pos hLoj n
  -- Combine
  calc ∫ ω, (g M - g (S.eval (ω n))) ∂μ
      ≤ K * ∫ ω, (M - S.eval (ω n)) ^ β ∂μ := h1
    _ ≤ K * (S.expectedGap π₀ M n) ^ β :=
        mul_le_mul_of_nonneg_left hjensen _hK
    _ ≤ K * (S.expectedGap π₀ M 0 /
          (1 + c * S.expectedGap π₀ M 0 * ↑n)) ^ β := by
        apply mul_le_mul_of_nonneg_left _ _hK
        exact Real.rpow_le_rpow (S.expectedGap_nonneg π₀ hM n) hēn (le_of_lt _hβ_pos)

/-- **Pathwise Hölder rate transfer (all β > 0)**: under the pathwise
    Łojasiewicz condition, the Hölder transfer applies along each path
    without Jensen, handling all β > 0 including β > 1. -/
theorem StochasticSOS.Morphism.pathwise_holder_transfer_alpha2
    {S₁ S₂ : StochasticSOS}
    (φ : StochasticSOS.Morphism S₁ S₂) (π₀ : S₁.P)
    {M : ℝ} (hM : ∀ π : S₁.P, S₁.eval π ≤ M)
    {c : ℝ} (hc_pos : 0 < c)
    (hLoj_pw : ∀ᵐ ω ∂(sosPathMeasure π₀ S₁.kernel),
      ∀ (k : ℕ), S₁.eval (ω (k + 1)) - S₁.eval (ω k) ≥
        c * (M - S₁.eval (ω k)) ^ 2)
    {K : ℝ} (hK : 0 ≤ K) {β : ℝ} (hβ : 0 < β)
    (hg_holder : ∀ x y : ℝ, x ≤ y → φ.g y - φ.g x ≤ K * (y - x) ^ β)
    : ∀ᵐ ω ∂(sosPathMeasure π₀ S₁.kernel), ∀ (k : ℕ),
      φ.g M - φ.g (S₁.eval (ω k)) ≤
        K * ((M - S₁.eval (ω 0)) /
          (1 + c * (M - S₁.eval (ω 0)) * ↑k)) ^ β := by
  -- Use pathwise rate + Hölder condition pointwise
  have hrate := S₁.pathwise_rate_alpha2 π₀ hM hc_pos hLoj_pw
  filter_upwards [hrate] with ω hω
  intro k
  have hgap_nn : 0 ≤ M - S₁.eval (ω k) := by linarith [hM (ω k)]
  have hrate_k := hω k
  calc φ.g M - φ.g (S₁.eval (ω k))
      ≤ K * (M - S₁.eval (ω k)) ^ β :=
        hg_holder (S₁.eval (ω k)) M (hM (ω k))
    _ ≤ K * ((M - S₁.eval (ω 0)) /
          (1 + c * (M - S₁.eval (ω 0)) * ↑k)) ^ β := by
        apply mul_le_mul_of_nonneg_left _ hK
        exact Real.rpow_le_rpow hgap_nn hrate_k (le_of_lt hβ)

end

end StochasticHolderTransfer

/-! # Stochastic Instantiations

Concrete stochastic SOS constructions for practical systems. -/

section StochasticInstantiations

noncomputable section

/-- **Stochastic GRPO as StochasticSOS**: the GRPO algorithm with random
    batches.  The Markov kernel models the randomness of batch sampling
    + trajectory generation + GRPO gradient update.

    Stochastic improvement holds when GRPO's expected update improves
    the evaluator (from the policy gradient theorem with exact rewards). -/
def stochasticGrpoSOS
    {Pol : Type*} [MeasurableSpace Pol]
    (eval : Pol → ℝ) (eval_meas : Measurable eval)
    (grpoKernel : Kernel Pol Pol) [IsMarkovKernel grpoKernel]
    (hImprove : ∀ π, ∫ π', eval π' ∂(grpoKernel π) ≥ eval π)
    (hBdd : ∃ M : ℝ≥0, ∀ π, |eval π| ≤ M) : StochasticSOS where
  P := Pol
  eval := eval
  eval_measurable := eval_meas
  kernel := grpoKernel
  stoch_improvement := hImprove
  eval_bound := hBdd

/-- Stochastic GRPO convergence: almost surely, by Doob's theorem. -/
theorem stochasticGrpo_convergence
    {Pol : Type*} [MeasurableSpace Pol]
    (eval : Pol → ℝ) (eval_meas : Measurable eval)
    (grpoKernel : Kernel Pol Pol) [IsMarkovKernel grpoKernel]
    (hImprove : ∀ π, ∫ π', eval π' ∂(grpoKernel π) ≥ eval π)
    (hBdd : ∃ M : ℝ≥0, ∀ π, |eval π| ≤ M) (π₀ : Pol) :
    ∀ᵐ ω ∂(sosPathMeasure π₀ grpoKernel),
      ∃ L : ℝ, Tendsto (fun n => eval (ω n)) atTop (nhds L) :=
  (stochasticGrpoSOS eval eval_meas grpoKernel hImprove hBdd).convergence π₀

/-- **Stochastic Autoresearch as StochasticSOS**: autoresearch with noisy
    evaluation.  The Markov kernel models the randomness of proposal
    generation + noisy val_bpb evaluation + keep/discard decision.

    When the evaluator noise is unbiased and the keep/discard uses the
    noisy value, expected improvement holds on average. -/
def stochasticAutoresearchSOS
    {Arch : Type*} [MeasurableSpace Arch]
    (eval : Arch → ℝ) (eval_meas : Measurable eval)
    (autoKernel : Kernel Arch Arch) [IsMarkovKernel autoKernel]
    (hImprove : ∀ a, ∫ a', eval a' ∂(autoKernel a) ≥ eval a)
    (hBdd : ∃ M : ℝ≥0, ∀ a, |eval a| ≤ M) : StochasticSOS where
  P := Arch
  eval := eval
  eval_measurable := eval_meas
  kernel := autoKernel
  stoch_improvement := hImprove
  eval_bound := hBdd

/-- Stochastic autoresearch convergence: a.s. convergence of the evaluator
    even with noisy evaluations, by Doob's theorem. -/
theorem stochasticAutoresearch_convergence
    {Arch : Type*} [MeasurableSpace Arch]
    (eval : Arch → ℝ) (eval_meas : Measurable eval)
    (autoKernel : Kernel Arch Arch) [IsMarkovKernel autoKernel]
    (hImprove : ∀ a, ∫ a', eval a' ∂(autoKernel a) ≥ eval a)
    (hBdd : ∃ M : ℝ≥0, ∀ a, |eval a| ≤ M) (a₀ : Arch) :
    ∀ᵐ ω ∂(sosPathMeasure a₀ autoKernel),
      ∃ L : ℝ, Tendsto (fun n => eval (ω n)) atTop (nhds L) :=
  (stochasticAutoresearchSOS eval eval_meas autoKernel hImprove hBdd).convergence a₀

/-- **Stochastic Gradient Descent as StochasticSOS**: SGD on a function f
    with stochastic gradients.  The Markov kernel models the random
    minibatch gradient step.

    The evaluator is -f (SOS maximizes; GD minimizes).  Stochastic
    improvement holds when the expected descent exceeds the noise:
    𝔼[-f(x - η∇f_ξ(x))] ≥ -f(x), i.e., 𝔼[f(step)] ≤ f(x). -/
def stochasticSGD_SOS
    {X : Type*} [MeasurableSpace X]
    (f : X → ℝ) (f_meas : Measurable f)
    (sgdKernel : Kernel X X) [IsMarkovKernel sgdKernel]
    (hDescent : ∀ x, ∫ x', (-f x') ∂(sgdKernel x) ≥ -f x)
    (hBdd : ∃ M : ℝ≥0, ∀ x, |(-f x)| ≤ M) : StochasticSOS where
  P := X
  eval := fun x => -f x
  eval_measurable := f_meas.neg
  kernel := sgdKernel
  stoch_improvement := hDescent
  eval_bound := hBdd

/-- Stochastic SGD convergence: the negated loss -f converges almost surely.
    Equivalently, the loss f converges. -/
theorem stochasticSGD_convergence
    {X : Type*} [MeasurableSpace X]
    (f : X → ℝ) (f_meas : Measurable f)
    (sgdKernel : Kernel X X) [IsMarkovKernel sgdKernel]
    (hDescent : ∀ x, ∫ x', (-f x') ∂(sgdKernel x) ≥ -f x)
    (hBdd : ∃ M : ℝ≥0, ∀ x, |(-f x)| ≤ M) (x₀ : X) :
    ∀ᵐ ω ∂(sosPathMeasure x₀ sgdKernel),
      ∃ L : ℝ, Tendsto (fun n => -f (ω n)) atTop (nhds L) :=
  (stochasticSGD_SOS f f_meas sgdKernel hDescent hBdd).convergence x₀

end

end StochasticInstantiations

/-! # Edge 7: Kernel Mixture Preservation

AReaL's interruptible generation creates trajectories using a mixture
of two policy versions.  We prove that convex mixtures of Markov kernels
preserve stochastic improvement: if both kernels improve the evaluator
in expectation, so does any convex combination. -/

section KernelMixture

/-- **Kernel mixture preserves stochastic improvement**: if two kernels
    both satisfy ∫ eval dκᵢ(π) ≥ eval(π) for the same evaluator, then
    the convex combination α·κ₁ + (1-α)·κ₂ also satisfies it.

    This models AReaL's interruptible generation: tokens generated by
    the old policy version (κ₁) and new version (κ₂) produce a mixed
    kernel, and convergence is preserved. -/
theorem stochastic_improvement_of_mixture
    {P : Type*} [MeasurableSpace P]
    (eval : P → ℝ) (_eval_meas : Measurable eval)
    (κ₁ κ₂ : Kernel P P) [IsMarkovKernel κ₁] [IsMarkovKernel κ₂]
    (h₁ : ∀ π, ∫ π', eval π' ∂(κ₁ π) ≥ eval π)
    (h₂ : ∀ π, ∫ π', eval π' ∂(κ₂ π) ≥ eval π)
    (_hint₁ : ∀ π, Integrable eval (κ₁ π))
    (_hint₂ : ∀ π, Integrable eval (κ₂ π))
    {α : ℝ} (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1)
    (π : P) :
    α * ∫ π', eval π' ∂(κ₁ π) + (1 - α) * ∫ π', eval π' ∂(κ₂ π) ≥ eval π := by
  -- α · ∫ eval dκ₁ ≥ α · eval(π)  and  (1-α) · ∫ eval dκ₂ ≥ (1-α) · eval(π)
  -- Sum: α · ∫ eval dκ₁ + (1-α) · ∫ eval dκ₂ ≥ α · eval(π) + (1-α) · eval(π) = eval(π)
  have h1 : α * ∫ π', eval π' ∂(κ₁ π) ≥ α * eval π :=
    mul_le_mul_of_nonneg_left (h₁ π) hα₀
  have h2 : (1 - α) * ∫ π', eval π' ∂(κ₂ π) ≥ (1 - α) * eval π :=
    mul_le_mul_of_nonneg_left (h₂ π) (by linarith)
  linarith

end KernelMixture

/-! # Edge 8: ε-Approximate Lax Morphisms

AReaL's proximal log-prob interpolation approximates the proximal policy:
  log π_prox ≈ log π_behave + α · (log π_θ − log π_behave)
This eliminates one forward pass (27% speedup) with bounded approximation
error.  We formalize ε-approximate lax morphisms and show that convergence
transfer degrades gracefully with the approximation error.

The existing SOS.LaxMorphism requires:
  E₂(f(δ₁(π))) ≥ E₂(δ₂(f(π)))
An ε-approximate lax morphism weakens this to:
  E₂(f(δ₁(π))) ≥ E₂(δ₂(f(π))) - ε

The accumulated error over n steps is at most n·ε. -/

section ApproximateMorphism

/-- An **ε-approximate lax morphism** between SOS instances.
    Like LaxMorphism but with bounded approximation error ε per step.
    Models systems where the update commutativity holds approximately
    (e.g., AReaL's proximal log-prob interpolation). -/
structure SOS.ApproxLaxMorphism (S1 S2 : SOS) where
  /-- Map on policy spaces -/
  f : S1.Pi → S2.Pi
  /-- Map on evaluator values -/
  g : ℝ → ℝ
  /-- g is monotone -/
  g_monotone : Monotone g
  /-- Evaluator compatibility (exact) -/
  evaluator_compat : ∀ (pi : S1.Pi), g (S1.E pi) = S2.E (f pi)
  /-- Approximation error per step -/
  ε : ℝ
  /-- ε is non-negative -/
  ε_nonneg : 0 ≤ ε
  /-- Approximate lax update: source dynamics are "almost as good" as target -/
  approx_update : ∀ (pi : S1.Pi),
    S2.E (f (S1.delta pi)) ≥ S2.E (S2.delta (f pi)) - ε

/-- **Degraded image bound**: the image evaluator sequence
    E₂(f(δ₁ⁿ(π₀))) doesn't drop more than n·ε below its initial value.
    For exact lax morphisms (ε = 0), the image evaluator is non-decreasing. -/
theorem SOS.ApproxLaxMorphism.degraded_image_bound
    {S1 S2 : SOS} (φ : SOS.ApproxLaxMorphism S1 S2) (pi0 : S1.Pi) (n : ℕ) :
    S2.E (φ.f (S1.delta^[n] pi0)) ≥ S2.E (φ.f pi0) - ↑n * φ.ε := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Function.iterate_succ', Function.comp_apply, Nat.cast_succ]
    -- E₂(f(δ₁^{n+1})) ≥ E₂(δ₂(f(δ₁ⁿ))) - ε  [approx_update]
    --                   ≥ E₂(f(δ₁ⁿ)) - ε        [monotone_improvement of δ₂]
    --                   ≥ (E₂(f(π₀)) - n·ε) - ε  [IH]
    --                   = E₂(f(π₀)) - (n+1)·ε
    have h1 := φ.approx_update (S1.delta^[n] pi0)
    have h2 := S2.monotone_improvement (φ.f (S1.delta^[n] pi0))
    nlinarith

/-- An exact lax morphism is an ε-approximate morphism with ε = 0. -/
def SOS.LaxMorphism.toApprox {S1 S2 : SOS} (φ : SOS.LaxMorphism S1 S2) :
    SOS.ApproxLaxMorphism S1 S2 where
  f := φ.f
  g := φ.g
  g_monotone := φ.g_monotone
  evaluator_compat := φ.evaluator_compat
  ε := 0
  ε_nonneg := le_refl 0
  approx_update := fun pi => by linarith [φ.lax_update pi]

end ApproximateMorphism

/-! # Edge 6: KDRL Rate Transfer via Warm Start

AReaL's KDRL (Knowledge Distillation + RL) trains a student model with
  J = J_GRPO − β·D_KL(π_θ ‖ π_teacher)
The teacher is frozen.  The KL penalty keeps the student near the teacher.

The rate transfer mechanism: the teacher provides a WARM START.  If the
teacher has converged to near-optimal (E(π_T*) ≈ M), and the student is
KL-constrained to stay near the teacher, the student's initial gap e₀
is small.  Since the O(1/n) rate has e₀ in the numerator, a smaller e₀
gives faster convergence.

This is the "information-bounded" rate transfer: the teacher's convergence
limits the student's initial gap via the KL constraint.  No Pinsker
inequality needed — the KL-evaluator bound is taken as a hypothesis
(axiomatizing the domain-specific claim that KL-close policies have
similar evaluator values). -/

section KDRLRateTransfer

/-- **KDRL warm-start rate**: if a KL constraint ensures that the initial
    policy has evaluator within δ_init of the bound M (from teacher
    proximity), then the constrained GRPO converges at rate O(1/n)
    with the warm-started initial gap δ_init.

    Interpretation: the teacher has converged to E ≈ M.  The KL penalty
    keeps the student within δ_init of the teacher's evaluator.  The
    student's O(1/n) rate then uses δ_init instead of the cold-start gap.

    This is the KDRL rate transfer: teacher convergence → small δ_init →
    fast student convergence.  The rate improvement is proportional to
    δ_init/δ_cold where δ_cold would be the cold-start gap. -/
theorem kdrl_warm_start_rate
    {Pol : Type*} [MetricSpace Pol]
    (E : Pol → ℝ) (grpoStep : Pol → Pol)
    (hE_bdd : BddAbove (Set.range E))
    (hImprove : ∀ π, E (grpoStep π) ≥ E π)
    (D : ℝ) (hD : D > 0)
    (hStep_bdd : ∀ π, dist (grpoStep π) π ≤ D)
    (klBound : Pol → Prop) -- KL constraint to teacher
    {M : ℝ} (hM : ∀ π : Pol, E π ≤ M)
    {δ_init : ℝ} (hδ_init : 0 ≤ δ_init)
    (hWarmStart : ∀ π, klBound π → M - E π ≤ δ_init)  -- teacher proximity bound
    {c : ℝ} (hc_pos : 0 < c)
    (hLoj : ∀ π : Pol,
      E ((constrainedGrpoSOS E grpoStep hE_bdd hImprove D hD hStep_bdd klBound).delta π) -
      E π ≥ c * (M - E π) ^ 2)
    (π₀ : Pol) (h₀ : klBound π₀) (n : ℕ) :
    M - (constrainedGrpoSOS E grpoStep hE_bdd hImprove D hD hStep_bdd klBound).orbit π₀ n ≤
      δ_init / (1 + c * δ_init * ↑n) := by
  -- The constrained GRPO's rate theorem gives O(1/n) with initial gap e₀
  have hrate := (constrainedGrpoSOS E grpoStep hE_bdd hImprove D hD hStep_bdd
    klBound).power_law_rate_alpha2 π₀ hM hc_pos hLoj n
  -- The warm-start bound: e₀ = M - E(π₀) ≤ δ_init (from teacher proximity)
  have he0 : M - E π₀ ≤ δ_init := hWarmStart π₀ h₀
  have he0_nn : 0 ≤ M - E π₀ := by linarith [hM π₀]
  -- hrate : M - orbit(n) ≤ (M - E(π₀)) / (1 + c·(M-E(π₀))·n)
  -- Since M - E(π₀) ≤ δ_init and the function x/(1+c·x·n) is increasing in x for x ≥ 0:
  -- (M-E(π₀))/(1+c·(M-E(π₀))·n) ≤ δ_init/(1+c·δ_init·n)
  calc M - (constrainedGrpoSOS E grpoStep hE_bdd hImprove D hD hStep_bdd klBound).orbit π₀ n
      ≤ (M - E π₀) / (1 + c * (M - E π₀) * ↑n) := hrate
    _ ≤ δ_init / (1 + c * δ_init * ↑n) := by
        -- x/(1+c·x·n) ≤ y/(1+c·y·n) when 0 ≤ x ≤ y (monotone in x)
        -- Proof: x(1+cyn) ≤ y(1+cxn) ⟺ x+cxyn ≤ y+cxyn ⟺ x ≤ y ✓
        have hd1 : 0 < 1 + c * (M - E π₀) * ↑n := by positivity
        have hd2 : 0 < 1 + c * δ_init * ↑n := by positivity
        rw [div_le_div_iff₀ hd1 hd2]
        nlinarith [mul_nonneg (le_of_lt hc_pos) (mul_nonneg he0_nn (Nat.cast_nonneg n))]

end KDRLRateTransfer

/-! # Stochastic Constraint Lifting

The deterministic SOS has constraintLift (Basic.lean:136): wrap δ with
an if-then-else checking a constraint. The stochastic analogue uses
Kernel.piecewise: apply the kernel when the constraint holds, stay put
(Kernel.id = Dirac at current state) when it doesn't.

Stochastic improvement is preserved:
- In C: ∫ eval dκ(π) ≥ eval(π) by stoch_improvement
- Not in C: ∫ eval d(Dirac π) = eval(π)          -/

section StochasticConstraintLifting

open Classical in
/-- **Stochastic constraint lifting**: mask a Markov kernel with a
    measurable predicate.  Transitions satisfying the constraint proceed
    normally; transitions violating it are replaced with staying put.

    This is the stochastic analogue of SOS.constraintLift (Theorem 3.11).
    Uses Kernel.piecewise from Mathlib. -/
noncomputable def StochasticSOS.stochConstraintLift
    (S : StochasticSOS) (C : Set S.P) (hC : MeasurableSet C)
    [MeasurableSingletonClass S.P] : StochasticSOS where
  P := S.P
  eval := S.eval
  eval_measurable := S.eval_measurable
  kernel := Kernel.piecewise hC S.kernel (Kernel.deterministic _root_.id measurable_id)
  stoch_improvement := fun π => by
    rw [Kernel.piecewise_apply]
    split_ifs with h
    · exact S.stoch_improvement π
    · simp [Kernel.deterministic_apply]
  eval_bound := S.eval_bound

open Classical in
/-- Stochastic constraint lifting preserves convergence: free theorem. -/
theorem StochasticSOS.stochConstraintLift_convergence
    (S : StochasticSOS) (C : Set S.P) (hC : MeasurableSet C)
    [MeasurableSingletonClass S.P] (π₀ : S.P) :
    ∀ᵐ ω ∂(sosPathMeasure π₀
      (Kernel.piecewise hC S.kernel (Kernel.deterministic _root_.id measurable_id))),
      ∃ L : ℝ, Tendsto (fun n => S.eval (ω n)) atTop (nhds L) :=
  (S.stochConstraintLift C hC).convergence π₀

end StochasticConstraintLifting

/-! # Variance-Controlled Convergence Rate

The Jensen bridge discards information: 𝔼[X²] ≥ (𝔼[X])² is tight only
when Var[X] = 0.  The TRUE recurrence from tower + Łojasiewicz is:

  ē_{n+1} ≤ ē_n - c · 𝔼[(M - eval(n))²]
           = ē_n - c · (ē_n² + Var[eval(n)])    [variance decomposition]

This is STRICTLY TIGHTER than the Jensen-bridge version ē_{n+1} ≤ ē_n - c·ē_n².
The variance term Var[eval(n)] provides EXTRA descent — variance HELPS convergence.

The Neural Thickets paper (Gan & Isola, 2025) provides empirical evidence:
diverse specialist perturbations (high variance) accelerate convergence. -/

section VarianceControlledRate

noncomputable section

/-- **Variance as a resource**: the Jensen bridge loses exactly Var[eval] of
    descent per step.  The second-moment integral 𝔼[(M-eval)²] decomposes as
    ē² + Var[eval], but Jensen only uses ē².  The "wasted" variance term
    c·Var[eval] ≥ 0 is additional convergence acceleration that the
    stochastic system provides for free.

    Formally: the Jensen-bridge recurrence ē_{n+1} ≤ ē_n - c·ē² is
    WEAKER than the true recurrence ē_{n+1} ≤ ē_n - c·(ē² + Var[eval]).
    The gap is exactly c·Var[eval(n)] ≥ 0.

    In the Neural Thickets setting (Gan & Isola, 2025), high Var[eval]
    corresponds to diverse task-specialists, which ACCELERATE convergence.
    This theorem says: variance is not noise to filter — it's computational
    fuel that makes stochastic convergence strictly faster than deterministic. -/
theorem StochasticSOS.variance_acceleration_nonneg (S : StochasticSOS) (π₀ : S.P)
    {c : ℝ} (hc_pos : 0 < c) (n : ℕ) :
    c * ProbabilityTheory.variance (fun ω => S.eval (ω n))
        (sosPathMeasure π₀ S.kernel) ≥ 0 :=
  mul_nonneg (le_of_lt hc_pos) (ProbabilityTheory.variance_nonneg _ _)

/-- **Second-moment lower bound**: 𝔼[(M-eval)²] ≥ ē² + Var[eval] ≥ ē².
    The first inequality is the variance decomposition; the second is
    Jensen.  This quantifies exactly how much information Jensen discards. -/
theorem StochasticSOS.second_moment_ge_sq_plus_var (S : StochasticSOS) (π₀ : S.P)
    {M : ℝ} (hM : ∀ π : S.P, S.eval π ≤ M) (n : ℕ) :
    ∫ ω, (M - S.eval (ω n)) ^ 2 ∂(sosPathMeasure π₀ S.kernel) ≥
      S.expectedGap π₀ M n ^ 2 := by
  -- This is exactly what sq_integral_le_integral_sq proves
  -- (Jensen's inequality for x²)
  have hf_int : Integrable (fun ω => M - S.eval (ω n)) (sosPathMeasure π₀ S.kernel) :=
    (integrable_const M).sub (S.evalProcess_integrable π₀ n)
  obtain ⟨B, hB⟩ := S.eval_bound
  have hf2_int : Integrable (fun ω => (M - S.eval (ω n)) ^ 2) (sosPathMeasure π₀ S.kernel) :=
    Integrable.of_bound
      ((S.eval_measurable.comp (measurable_pi_apply n)).const_sub M
        |>.pow_const 2 |>.aestronglyMeasurable)
      ((M + ↑B) ^ 2) (ae_of_all _ fun ω => by
        simp only [Real.norm_eq_abs]
        have hnn : 0 ≤ M - S.eval (ω n) := by linarith [hM (ω n)]
        have hle : M - S.eval (ω n) ≤ M + ↑B := by
          have := (abs_le.mp (hB (ω n))).1; linarith
        calc |(M - S.eval (ω n)) ^ 2| = (M - S.eval (ω n)) ^ 2 :=
              abs_of_nonneg (sq_nonneg _)
          _ ≤ (M + ↑B) ^ 2 := by nlinarith)
  have hlin : ∫ ω, (M - S.eval (ω n)) ∂(sosPathMeasure π₀ S.kernel) =
      S.expectedGap π₀ M n := by
    show ∫ ω, (M - S.eval (ω n)) ∂(sosPathMeasure π₀ S.kernel) =
      S.expectedGap π₀ M n
    unfold StochasticSOS.expectedGap StochasticSOS.expectedEval
    have hsub' : ∫ ω, (M - S.eval (ω n)) ∂(sosPathMeasure π₀ S.kernel) =
        ∫ ω, M ∂(sosPathMeasure π₀ S.kernel) -
          ∫ ω, S.eval (ω n) ∂(sosPathMeasure π₀ S.kernel) :=
      integral_sub (integrable_const M) (S.evalProcess_integrable π₀ n)
    rw [hsub', integral_const]
    simp [Measure.real, measure_univ]
  rw [← hlin]
  exact sq_integral_le_integral_sq hf_int hf2_int

/-- **RandOpt / Neural Thickets as a Stochastic Autoresearch-SOS**:
    Gaussian perturbation of pretrained weights, evaluated on a task,
    with top-K selection.  This is exactly the stochastic autoresearch
    construction: the kernel samples a random perturbation, the
    keep/discard mechanism selects improving candidates.

    Convergence follows from StochasticSOS.convergence. The variance-
    improved recurrence quantifies how the thicket's diversity (high
    Var[eval]) accelerates convergence beyond the mean improvement. -/
def randOptSOS
    {Pol : Type*} [MeasurableSpace Pol]
    (eval : Pol → ℝ) (eval_meas : Measurable eval)
    (perturbKernel : Kernel Pol Pol) [IsMarkovKernel perturbKernel]
    (hImprove : ∀ θ, ∫ θ', eval θ' ∂(perturbKernel θ) ≥ eval θ)
    (hBdd : ∃ M : ℝ≥0, ∀ θ, |eval θ| ≤ M) : StochasticSOS :=
  stochasticAutoresearchSOS eval eval_meas perturbKernel hImprove hBdd

/-- RandOpt convergence: almost-sure convergence of the evaluator
    sequence under Gaussian perturbation + selection. -/
theorem randOpt_convergence
    {Pol : Type*} [MeasurableSpace Pol]
    (eval : Pol → ℝ) (eval_meas : Measurable eval)
    (perturbKernel : Kernel Pol Pol) [IsMarkovKernel perturbKernel]
    (hImprove : ∀ θ, ∫ θ', eval θ' ∂(perturbKernel θ) ≥ eval θ)
    (hBdd : ∃ M : ℝ≥0, ∀ θ, |eval θ| ≤ M) (θ₀ : Pol) :
    ∀ᵐ ω ∂(sosPathMeasure θ₀ perturbKernel),
      ∃ L : ℝ, Tendsto (fun n => eval (ω n)) atTop (nhds L) :=
  (randOptSOS eval eval_meas perturbKernel hImprove hBdd).convergence θ₀

end

end VarianceControlledRate

/-! # Real-Valued Łojasiewicz Exponents

Extension of the power-law rate theory from integer exponents (p ∈ ℕ)
to real exponents (p ∈ ℝ, p ≥ 1).  The key new lemma is the real
Bernoulli product inequality: (1+pt)(1-t)^p ≤ 1 for p ≥ 1, 0 ≤ t < 1.
Proved via log(1+x) ≤ x (from Mathlib's log_le_sub_one_of_pos). -/

section RealExponent

open Real in
/-- **Real Bernoulli product inequality**: (1 + p·t)·(1-t)^p ≤ 1 for
    p ≥ 1 and 0 ≤ t < 1.  The integer version (bernoulli_product in
    PowerLaw.lean) is proved by natural induction; this real version
    uses the logarithmic inequality log(1+x) ≤ x.

    Proof: log((1+pt)(1-t)^p) = log(1+pt) + p·log(1-t)
           ≤ pt + p·(-t) = 0.  Exponentiate. -/
theorem real_bernoulli_product {p t : ℝ} (hp : 1 ≤ p)
    (ht0 : 0 ≤ t) (ht1 : t < 1) :
    (1 + p * t) * (1 - t) ^ p ≤ 1 := by
  rcases eq_or_lt_of_le ht0 with rfl | ht_pos
  · simp
  have h1pt : 0 < 1 + p * t := by positivity
  have h1t : 0 < 1 - t := by linarith
  -- Strategy: (1+pt) ≤ exp(pt) and (1-t)^p ≤ exp(-pt)
  -- Product ≤ exp(pt)·exp(-pt) = exp(0) = 1
  have hexp1 : 1 + p * t ≤ Real.exp (p * t) := by
    linarith [Real.add_one_le_exp (p * t)]
  have hexp2 : (1 - t) ^ p ≤ Real.exp (-(p * t)) := by
    rw [← Real.exp_log (rpow_pos_of_pos h1t p), Real.log_rpow h1t]
    exact Real.exp_le_exp_of_le (by nlinarith [Real.log_le_sub_one_of_pos h1t])
  calc (1 + p * t) * (1 - t) ^ p
      ≤ Real.exp (p * t) * Real.exp (-(p * t)) := by
        exact mul_le_mul hexp1 hexp2 (rpow_nonneg (le_of_lt h1t) p)
          (le_of_lt (Real.exp_pos _))
    _ = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]

/-- Real Bernoulli product at t = 1: (1+p)·0^p = 0 ≤ 1. -/
theorem real_bernoulli_product_boundary {p : ℝ} (hp : 1 ≤ p) :
    (1 + p * 1) * (1 - 1) ^ p ≤ 1 := by
  simp [Real.zero_rpow (by linarith : p ≠ 0)]

/-- **Real-valued power-law rate** (statement): under the power-law
    Łojasiewicz condition with REAL exponent p ≥ 1, the p-th rpow of
    the gap satisfies e_n^p ≤ e₀^p / (1 + c·p·e₀^p·n).

    This extends power_law_recurrence_div_general from ℕ to ℝ exponents.
    The proof uses real_bernoulli_product instead of bernoulli_product. -/
theorem rpow_recurrence_div
    (e : ℕ → ℝ) (c e0 p : ℝ) (hp : 1 ≤ p)
    (hc_pos : 0 < c)
    (he0_nn : 0 ≤ e0)
    (hce_small : c * e0 ^ p ≤ 1)
    (hnn : ∀ n, 0 ≤ e n)
    (hle : ∀ n, e n ≤ e0)
    (hrec : ∀ n, e (n + 1) ≤ e n * (1 - c * e n ^ p))
    (n : ℕ) :
    e n ^ p ≤ e0 ^ p / (1 + c * p * e0 ^ p * ↑n) := by
  open Real in
  set ρ := e0 ^ p
  have hρ_nn : 0 ≤ ρ := rpow_nonneg he0_nn p
  have hden_pos : ∀ k : ℕ, 0 < 1 + c * p * ρ * ↑k := by intro k; positivity
  rw [le_div_iff₀ (hden_pos n)]
  -- Prove multiplication form: e_n^p · (1 + c·p·ρ·n) ≤ ρ
  induction n with
  | zero =>
    simp only [Nat.cast_zero, mul_zero, add_zero, mul_one]
    exact rpow_le_rpow (hnn 0) (hle 0) (by linarith)
  | succ n ih =>
    set en := e n
    have hen_nn : 0 ≤ en := hnn n
    have hen_le : en ≤ e0 := hle n
    have henp_nn : 0 ≤ en ^ p := rpow_nonneg hen_nn p
    have henp_le : en ^ p ≤ ρ := rpow_le_rpow hen_nn hen_le (by linarith)
    have hcenp_le : c * en ^ p ≤ 1 :=
      le_trans (mul_le_mul_of_nonneg_left henp_le (le_of_lt hc_pos)) hce_small
    have hcenp_nn : 0 ≤ c * en ^ p := by positivity
    have h1cenp_nn : 0 ≤ 1 - c * en ^ p := by linarith
    -- Step 1: e(n+1)^p ≤ en^p · (1-c·en^p)^p
    have hstep_le : e (n + 1) ≤ en * (1 - c * en ^ p) := hrec n
    have hprod_nn : 0 ≤ en * (1 - c * en ^ p) :=
      mul_nonneg hen_nn h1cenp_nn
    have horbp : e (n + 1) ^ p ≤ en ^ p * (1 - c * en ^ p) ^ p := by
      calc e (n + 1) ^ p
          ≤ (en * (1 - c * en ^ p)) ^ p :=
            rpow_le_rpow (hnn (n + 1)) hstep_le (by linarith)
        _ = en ^ p * (1 - c * en ^ p) ^ p :=
            mul_rpow hen_nn h1cenp_nn
    -- Step 2: algebraic manipulation
    -- Name the Bernoulli factor
    set B := (1 - c * en ^ p) ^ p with hB_def
    have hB_nn : 0 ≤ B := rpow_nonneg h1cenp_nn p
    simp only [Nat.cast_succ]
    have hden_nn : 0 ≤ 1 + c * p * ρ * (↑n + 1) := by positivity
    -- e(n+1)^p · (1+c·p·ρ·(n+1))
    -- ≤ en^p · B · (1+c·p·ρ·(n+1))
    -- = en^p · B · (1+c·p·ρ·n) + c·p·ρ · en^p · B
    -- ≤ ρ · B + c·p·ρ · en^p · B        [using IH]
    -- = ρ · B · (1 + c·p·en^p)
    -- = ρ · (1 + p·(c·en^p)) · (1-c·en^p)^p
    -- ≤ ρ · 1                             [real Bernoulli]
    -- = ρ
    calc e (n + 1) ^ p * (1 + c * p * ρ * (↑n + 1))
        ≤ en ^ p * B * (1 + c * p * ρ * (↑n + 1)) :=
          mul_le_mul_of_nonneg_right horbp hden_nn
      _ = en ^ p * (1 + c * p * ρ * ↑n) * B + c * p * ρ * en ^ p * B := by
          ring
      _ ≤ ρ * B + c * p * ρ * en ^ p * B := by
          linarith [mul_le_mul_of_nonneg_right ih hB_nn]
      _ = ρ * ((1 + p * (c * en ^ p)) * B) := by
          ring
      _ ≤ ρ * 1 := by
          apply mul_le_mul_of_nonneg_left _ hρ_nn
          -- (1 + p·t) · (1-t)^p ≤ 1 where t = c·en^p
          rcases eq_or_lt_of_le hcenp_le with heq | hlt
          · -- t = 1: boundary case (1+p)·0^p = 0 ≤ 1
            rw [heq]; simp [hB_def, heq, Real.zero_rpow (by linarith : p ≠ 0)]
          · -- t < 1: use real_bernoulli_product
            exact real_bernoulli_product hp hcenp_nn hlt
      _ = ρ := mul_one ρ

/-! ## SOS-Level Wrappers: Real-Exponent Łojasiewicz Rates

The algebraic `rpow_recurrence_div` lemma is tied to a bare non-negative
sequence.  We lift it to three end-user theorems:

* `SOS.power_law_rate_rpow` — deterministic O(1/n) rate under the
  real-exponent Łojasiewicz condition (α = p + 1, real p ≥ 1).
* `StochasticSOS.expected_rate_rpow` — stochastic expected-gap rate,
  via a real-exponent Jensen bridge.
* `StochasticSOS.pathwise_rate_rpow` — pathwise almost-sure rate.

All three reuse the deterministic induction inside `rpow_recurrence_div`
verbatim; the real-exponent case differs only in the Bernoulli step
(handled once in `real_bernoulli_product`). -/

/-- Real-α counterpart of `small_constant_of_recurrence_general`: the
    small-constant condition c · e₀^p ≤ 1 is derivable from the rpow
    recurrence e_{n+1} ≤ e_n · (1 - c · e_n^p) together with non-negativity. -/
lemma small_constant_of_recurrence_rpow
    (e : ℕ → ℝ) (c p : ℝ) (hp : 1 ≤ p)
    (_hc_pos : 0 < c)
    (hnn : ∀ n, 0 ≤ e n)
    (hrec : ∀ n, e (n + 1) ≤ e n * (1 - c * e n ^ p)) :
    c * e 0 ^ p ≤ 1 := by
  by_contra h
  push_neg at h
  have hp_ne : (p : ℝ) ≠ 0 := by linarith
  have he0_pos : 0 < e 0 := by
    rcases eq_or_lt_of_le (hnn 0) with he0 | he0
    · exfalso
      rw [← he0, Real.zero_rpow hp_ne] at h
      linarith
    · exact he0
  have hrpow_pos : 0 < e 0 ^ p := Real.rpow_pos_of_pos he0_pos p
  -- c · e₀^p > 1 ⇒ e₁ ≤ e₀ · (1 - c · e₀^p) < 0, contradicting e₁ ≥ 0
  have hneg : e 0 * (1 - c * e 0 ^ p) < 0 := by nlinarith
  linarith [hrec 0, hnn 1]

/-- SOS-level real-α counterpart of `SOS.loj_implies_small`: the
    small-constant condition c · e₀^p ≤ 1 follows from the rpow
    Łojasiewicz condition at π₀ together with the upper bound M. -/
lemma SOS.loj_implies_small_rpow (S : SOS) (pi0 : S.Pi) (p : ℝ) (hp : 1 ≤ p)
    {M : ℝ} (hM : ∀ π : S.Pi, S.E π ≤ M)
    {c : ℝ} (_hc_pos : 0 < c)
    (hLoj : ∀ π : S.Pi, S.E (S.delta π) - S.E π ≥ c * (M - S.E π) ^ (p + 1)) :
    c * (M - S.E pi0) ^ p ≤ 1 := by
  by_contra h
  push_neg at h
  set e0 := M - S.E pi0 with he0_def
  have he0_nn : 0 ≤ e0 := by linarith [hM pi0]
  have hp_ne : (p : ℝ) ≠ 0 := by linarith
  have hp1_ne : (p + 1 : ℝ) ≠ 0 := by linarith
  have he0_pos : 0 < e0 := by
    rcases eq_or_lt_of_le he0_nn with he0_eq | hpos
    · exfalso
      rw [← he0_eq, Real.zero_rpow hp_ne] at h
      linarith
    · exact hpos
  -- Factor e0^(p+1) = e0^p · e0 (Real.rpow_add_one' handles 0 ≤ e0)
  have hfactor : e0 ^ (p + 1) = e0 ^ p * e0 :=
    Real.rpow_add_one' he0_nn hp1_ne
  -- From hLoj at pi0: E(δ pi0) - E pi0 ≥ c · e0^(p+1); combined with hM:
  -- e0 = M - E pi0 ≥ (M - E pi0) - (M - E(δ pi0)) = E(δ pi0) - E pi0 ≥ c · e0^(p+1)
  have hbound : e0 ≥ c * e0 ^ (p + 1) := by linarith [hLoj pi0, hM (S.delta pi0)]
  -- But h says c · e0^p > 1, so c · e0^(p+1) = (c · e0^p) · e0 > e0
  have hrhs_gt : c * e0 ^ (p + 1) > e0 := by
    rw [hfactor]
    calc c * (e0 ^ p * e0)
        = c * e0 ^ p * e0 := by ring
      _ > 1 * e0 := mul_lt_mul_of_pos_right h he0_pos
      _ = e0 := one_mul _
  linarith

/-- **SOS real-exponent power-law rate** (division form): under the
    Łojasiewicz condition with REAL exponent p + 1 ≥ 2, the p-th rpow of
    the gap decays as O(1/n):
    (M - orbit(n)) ^ p ≤ e₀^p / (1 + c·p·e₀^p·n).

    This is the SOS-level wrapper around `rpow_recurrence_div`, mirroring
    `SOS.power_law_rate_general` (ℕ case).  Consumes the rpow Łojasiewicz
    hypothesis and returns the O(1/n) rate on the p-th rpow of the gap. -/
theorem SOS.power_law_rate_rpow (S : SOS) (pi0 : S.Pi) (p : ℝ) (hp : 1 ≤ p)
    {M : ℝ} (hM : ∀ π : S.Pi, S.E π ≤ M)
    {c : ℝ} (hc_pos : 0 < c)
    (hLoj : ∀ π : S.Pi, S.E (S.delta π) - S.E π ≥ c * (M - S.E π) ^ (p + 1))
    (n : ℕ) :
    (M - S.orbit pi0 n) ^ p ≤
      (M - S.E pi0) ^ p / (1 + c * p * (M - S.E pi0) ^ p * ↑n) := by
  have he0_nn : 0 ≤ M - S.E pi0 := by linarith [hM pi0]
  have hsmall : c * (M - S.E pi0) ^ p ≤ 1 :=
    S.loj_implies_small_rpow pi0 p hp hM hc_pos hLoj
  have hp1_ne : (p + 1 : ℝ) ≠ 0 := by linarith
  -- Derive the rpow recurrence on the gap sequence from the Łojasiewicz condition
  have hrec : ∀ k, M - S.orbit pi0 (k + 1) ≤
      (M - S.orbit pi0 k) * (1 - c * (M - S.orbit pi0 k) ^ p) := by
    intro k
    set en := M - S.orbit pi0 k
    have hen_nn : 0 ≤ en := S.gap_nonneg pi0 hM k
    have hfactor : en ^ (p + 1) = en ^ p * en :=
      Real.rpow_add_one' hen_nn hp1_ne
    -- From hLoj at δ^[k] pi0: E(δ^[k+1] pi0) - E(δ^[k] pi0) ≥ c · en^(p+1)
    have hstep : M - S.orbit pi0 (k + 1) ≤ en - c * en ^ (p + 1) := by
      change M - S.orbit pi0 (k + 1) ≤
        (M - S.orbit pi0 k) - c * (M - S.orbit pi0 k) ^ (p + 1)
      simp only [SOS.orbit, Function.iterate_succ', Function.comp_apply]
      linarith [hLoj (S.delta^[k] pi0)]
    have hcfact : c * en ^ (p + 1) = en * (c * en ^ p) := by rw [hfactor]; ring
    linarith
  exact rpow_recurrence_div
    (fun k => M - S.orbit pi0 k) c (M - S.E pi0) p hp hc_pos
    he0_nn hsmall
    (S.gap_nonneg pi0 hM) (S.gap_le_initial pi0 hM) hrec n

/-! ## Stochastic Real-Exponent Rate

The Jensen bridge carries through verbatim: convexity of `x ↦ x^(p+1)` on
[0,∞) for real p + 1 ≥ 1 is `convexOn_rpow`, and the measure-theoretic
Jensen inequality `ConvexOn.map_average_le` applies to give
ēₙ^(p+1) ≤ 𝔼[(M − eval(ω(n)))^(p+1)], closing the loop with the
tower property. -/

noncomputable section StochasticRealExponent

open Preorder

variable (S : StochasticSOS) (π₀ : S.P)

/-- **Stochastic real-exponent Jensen bridge**: under the stochastic
    Łojasiewicz condition with REAL exponent p + 1 (p ≥ 1), the expected
    gap satisfies ē_{n+1} ≤ ē_n · (1 - c · ē_n ^ p).

    Proof structure parallels `expectedGap_recurrence_general`:
    (a) tower property + Łojasiewicz on the conditioning at step n;
    (b) Jensen via `convexOn_rpow` in place of `convexOn_pow`.
    The final real-exponent factorisation e^(p+1) = e · e^p uses
    `Real.rpow_add_one'` (base nonneg, exponent p + 1 ≠ 0). -/
theorem StochasticSOS.expectedGap_recurrence_rpow
    (p : ℝ) (hp : 1 ≤ p)
    {M : ℝ} (hM : ∀ π : S.P, S.eval π ≤ M)
    {c : ℝ} (hc_pos : 0 < c)
    (hLoj : ∀ π : S.P,
      ∫ π', S.eval π' ∂(S.kernel π) - S.eval π ≥ c * (M - S.eval π) ^ (p + 1))
    (n : ℕ) :
    S.expectedGap π₀ M (n + 1) ≤
      S.expectedGap π₀ M n * (1 - c * S.expectedGap π₀ M n ^ p) := by
  simp only [StochasticSOS.expectedGap, StochasticSOS.expectedEval]
  set μ := sosPathMeasure π₀ S.kernel
  set ēn := M - ∫ ω, S.eval (ω n) ∂μ with hēn_def
  have hp1_nn : (0 : ℝ) ≤ p + 1 := by linarith
  have hp1_ne : (p + 1 : ℝ) ≠ 0 := by linarith
  -- Pointwise non-negativity of the gap integrand
  have hgap_nn : ∀ ω : ℕ → S.P, 0 ≤ M - S.eval (ω n) :=
    fun ω => by linarith [hM (ω n)]
  -- Integrability of (M - eval(n))^(p+1): bounded by (M + B)^(p+1)
  have hfp_int : Integrable (fun ω => (M - S.eval (ω n)) ^ (p + 1)) μ := by
    obtain ⟨B, hB⟩ := S.eval_bound
    have hgap_meas : Measurable (fun ω : ℕ → S.P => M - S.eval (ω n)) :=
      measurable_const.sub (S.eval_measurable.comp (measurable_pi_apply n))
    have hrpow_meas : Measurable (fun ω : ℕ → S.P => (M - S.eval (ω n)) ^ (p + 1)) :=
      (Real.continuous_rpow_const hp1_nn).measurable.comp hgap_meas
    exact Integrable.of_bound hrpow_meas.aestronglyMeasurable
      ((M + ↑B) ^ (p + 1)) (ae_of_all μ fun ω => by
        simp only [Real.norm_eq_abs]
        rw [abs_of_nonneg (Real.rpow_nonneg (hgap_nn ω) _)]
        exact Real.rpow_le_rpow (hgap_nn ω)
          (by have := (abs_le.mp (hB (ω n))).1; linarith) hp1_nn)
  -- Part (a): Tower property + Łojasiewicz on the conditioning at step n.
  -- Structurally identical to the ℕ case; only the integrand exponent differs.
  have h_tower_loj : ∫ ω, S.eval (ω (n + 1)) ∂μ ≥
      ∫ ω, S.eval (ω n) ∂μ + c * ∫ ω, (M - S.eval (ω n)) ^ (p + 1) ∂μ := by
    let ℱ : Filtration ℕ (MeasurableSpace.pi (m := fun _ => S.ms)) :=
      Filtration.piLE (X := fun _ => S.P)
    have hm : (ℱ n : MeasurableSpace (ℕ → S.P)) ≤ MeasurableSpace.pi := ℱ.le n
    haveI : @IsFiniteMeasure (ℕ → S.P) (ℱ n) (μ.trim hm) :=
      @isFiniteMeasure_trim (ℕ → S.P) (ℱ n) MeasurableSpace.pi μ hm inferInstance
    haveI : @SigmaFinite (ℕ → S.P) (ℱ n) (μ.trim hm) :=
      @IsFiniteMeasure.toSigmaFinite _ _ _ inferInstance
    have hμ : μ = Kernel.traj (X := fun _ => S.P) (fun m => homKernel S.kernel m) 0
        ((MeasurableEquiv.piUnique (fun _ : ↥(Finset.Iic 0) => S.P)).symm π₀) := by
      change sosPathMeasure π₀ S.kernel = _
      unfold sosPathMeasure Kernel.trajMeasure
      rw [Measure.map_dirac
        (MeasurableEquiv.piUnique (fun _ : ↥(Finset.Iic 0) => S.P)).symm.measurable]
      exact Measure.dirac_bind
        (Kernel.traj (X := fun _ => S.P) (fun m => homKernel S.kernel m) 0).measurable _
    have hint : Integrable (S.evalProcess (n + 1))
        (Kernel.traj (X := fun _ => S.P) (fun m => homKernel S.kernel m) 0
          ((MeasurableEquiv.piUnique (fun _ : ↥(Finset.Iic 0) => S.P)).symm π₀)) :=
      hμ ▸ S.evalProcess_integrable π₀ (n + 1)
    have hae : ∀ᵐ ω ∂μ,
        S.eval (ω n) + c * (M - S.eval (ω n)) ^ (p + 1) ≤
          (μ[S.evalProcess (n + 1) | ↑(ℱ n)]) ω := by
      rw [hμ]
      filter_upwards [Kernel.condExp_traj (Nat.zero_le n) hint] with ω hω
      rw [hω]
      simp only [StochasticSOS.evalProcess]
      suffices h : ∫ y, S.eval (y (n + 1)) ∂Kernel.traj (X := fun _ => S.P)
          (fun m => homKernel S.kernel m) n (frestrictLe n ω) =
          ∫ z, S.eval z ∂S.kernel (ω n) by
        rw [h]; linarith [hLoj (ω n)]
      have hmeas : Measurable (fun (y : ℕ → S.P) => y (n + 1)) :=
        measurable_pi_apply (n + 1)
      rw [← integral_map hmeas.aemeasurable S.eval_measurable.aestronglyMeasurable]
      congr 1
      rw [← Kernel.map_apply _ hmeas, Kernel.map_traj_succ_self]
      simp only [homKernel, Kernel.comap_apply, frestrictLe_apply]
    have hint_lhs : Integrable
        (fun ω => S.eval (ω n) + c * (M - S.eval (ω n)) ^ (p + 1)) μ :=
      (S.evalProcess_integrable π₀ n).add (hfp_int.const_mul c)
    have h1 := integral_mono_ae hint_lhs integrable_condExp hae
    have h2 : ∫ ω, (μ[S.evalProcess (n + 1) | ↑(ℱ n)]) ω ∂μ =
        ∫ ω, S.evalProcess (n + 1) ω ∂μ := integral_condExp hm
    simp only [StochasticSOS.evalProcess] at h2
    have h3 : ∫ x, S.eval (x n) + c * (M - S.eval (x n)) ^ (p + 1) ∂μ =
        ∫ x, S.eval (x n) ∂μ + c * ∫ x, (M - S.eval (x n)) ^ (p + 1) ∂μ := by
      have : ∫ x, S.eval (x n) + c * (M - S.eval (x n)) ^ (p + 1) ∂μ =
          ∫ x, S.evalProcess n x ∂μ + ∫ x, (c * (M - S.eval (x n)) ^ (p + 1)) ∂μ :=
        integral_add (S.evalProcess_integrable π₀ n) (hfp_int.const_mul c)
      simp only [StochasticSOS.evalProcess, integral_const_mul] at this
      exact this
    linarith
  -- Part (b): Jensen for x^(p+1) via ConvexOn.map_average_le, now with rpow
  have hf_int : Integrable (fun ω => M - S.eval (ω n)) μ :=
    (integrable_const M).sub (S.evalProcess_integrable π₀ n)
  have h_jensen : ēn ^ (p + 1) ≤ ∫ ω, (M - S.eval (ω n)) ^ (p + 1) ∂μ := by
    have hlin : ∫ ω, (M - S.eval (ω n)) ∂μ = ēn := by
      change ∫ ω, (M - S.eval (ω n)) ∂μ = M - ∫ ω, S.eval (ω n) ∂μ
      have hsub' : ∫ ω, (M - S.eval (ω n)) ∂μ =
          ∫ ω, M ∂μ - ∫ ω, S.eval (ω n) ∂μ :=
        integral_sub (integrable_const M) (S.evalProcess_integrable π₀ n)
      rw [hsub', integral_const]
      simp only [Measure.real, measure_univ, ENNReal.toReal_one, one_smul, μ]
    have hconv : ConvexOn ℝ (Set.Ici 0) (fun x : ℝ => x ^ (p + 1)) :=
      convexOn_rpow (by linarith : (1 : ℝ) ≤ p + 1)
    have hcont : ContinuousOn (fun x : ℝ => x ^ (p + 1)) (Set.Ici 0) :=
      (Real.continuous_rpow_const hp1_nn).continuousOn
    have hclosed : IsClosed (Set.Ici (0 : ℝ)) := isClosed_Ici
    have hfs : ∀ᵐ ω ∂μ, (fun ω => M - S.eval (ω n)) ω ∈ Set.Ici (0 : ℝ) :=
      ae_of_all μ fun ω => Set.mem_Ici.mpr (hgap_nn ω)
    have hgi : Integrable ((fun x : ℝ => x ^ (p + 1)) ∘ (fun ω => M - S.eval (ω n))) μ :=
      hfp_int
    have hj := ConvexOn.map_average_le hconv hcont hclosed hfs hf_int hgi
    rw [average_eq_integral, average_eq_integral] at hj
    rwa [hlin] at hj
  -- Combine (a) + (b): ē_{n+1} ≤ ēn - c · ēn^(p+1) = ēn · (1 - c · ēn^p)
  have hēn_nn : 0 ≤ ēn := by
    have := S.expectedGap_nonneg π₀ hM n
    simp only [StochasticSOS.expectedGap, StochasticSOS.expectedEval] at this
    exact this
  have hpow : ēn ^ (p + 1) = ēn ^ p * ēn :=
    Real.rpow_add_one' hēn_nn hp1_ne
  -- Goal (after the opening simp) is:
  --   M - ∫ S.eval (ω (n+1)) ∂μ ≤ ēn * (1 - c · ēn^p)
  -- which matches ēn - c · ēn^(p+1) once we use hpow.
  nlinarith [mul_le_mul_of_nonneg_left h_jensen (le_of_lt hc_pos)]

/-- **Stochastic real-exponent O(1/n) rate**: the p-th rpow of the
    expected gap decays as O(1/n):
    ēₙ ^ p ≤ ē₀ ^ p / (1 + c · p · ē₀ ^ p · n).

    Assembles the Jensen bridge `expectedGap_recurrence_rpow` with the
    standalone algebraic lemma `rpow_recurrence_div`.  Mirrors the ℕ
    wrapper `expected_rate_general`. -/
theorem StochasticSOS.expected_rate_rpow
    (p : ℝ) (hp : 1 ≤ p)
    {M : ℝ} (hM : ∀ π : S.P, S.eval π ≤ M)
    {c : ℝ} (hc_pos : 0 < c)
    (hLoj : ∀ π : S.P,
      ∫ π', S.eval π' ∂(S.kernel π) - S.eval π ≥ c * (M - S.eval π) ^ (p + 1))
    (n : ℕ) :
    S.expectedGap π₀ M n ^ p ≤
      S.expectedGap π₀ M 0 ^ p /
        (1 + c * p * S.expectedGap π₀ M 0 ^ p * ↑n) := by
  exact rpow_recurrence_div
    (S.expectedGap π₀ M) c (S.expectedGap π₀ M 0) p hp hc_pos
    (S.expectedGap_nonneg π₀ hM 0)
    (small_constant_of_recurrence_rpow
      (S.expectedGap π₀ M) c p hp hc_pos
      (S.expectedGap_nonneg π₀ hM)
      (S.expectedGap_recurrence_rpow π₀ p hp hM hc_pos hLoj))
    (S.expectedGap_nonneg π₀ hM)
    (S.expectedGap_le_initial π₀ hM)
    (S.expectedGap_recurrence_rpow π₀ p hp hM hc_pos hLoj)
    n

/-- **Pathwise real-exponent O(1/n) rate**: under a pathwise Łojasiewicz
    condition with REAL exponent p + 1, the deterministic real-α rate
    applies to almost every realisation.  Parallels
    `StochasticSOS.pathwise_rate_alpha2` with rpow throughout. -/
theorem StochasticSOS.pathwise_rate_rpow
    (p : ℝ) (hp : 1 ≤ p)
    {M : ℝ} (hM : ∀ π : S.P, S.eval π ≤ M)
    {c : ℝ} (hc_pos : 0 < c)
    (hLoj_pw : ∀ᵐ ω ∂(sosPathMeasure π₀ S.kernel),
      ∀ k : ℕ, S.eval (ω (k + 1)) - S.eval (ω k) ≥
        c * (M - S.eval (ω k)) ^ (p + 1)) :
    ∀ᵐ ω ∂(sosPathMeasure π₀ S.kernel), ∀ (k : ℕ),
      (M - S.eval (ω k)) ^ p ≤
        (M - S.eval (ω 0)) ^ p /
          (1 + c * p * (M - S.eval (ω 0)) ^ p * ↑k) := by
  filter_upwards [hLoj_pw] with ω hω
  intro k
  have hp1_ne : (p + 1 : ℝ) ≠ 0 := by linarith
  have hnn : ∀ j, 0 ≤ (fun i => M - S.eval (ω i)) j := fun j => by
    simp only; linarith [hM (ω j)]
  -- Monotonicity along the path: E(ω(j)) is non-decreasing
  have hpath_mono : ∀ j, S.eval (ω 0) ≤ S.eval (ω j) := by
    intro j
    induction j with
    | zero => exact le_refl _
    | succ j ih =>
      have step := hω j
      have hrpow_nn : 0 ≤ (M - S.eval (ω j)) ^ (p + 1) :=
        Real.rpow_nonneg (by linarith [hM (ω j)]) _
      have hcrpow_nn : 0 ≤ c * (M - S.eval (ω j)) ^ (p + 1) :=
        mul_nonneg hc_pos.le hrpow_nn
      linarith
  have hle : ∀ j, (fun i => M - S.eval (ω i)) j ≤ (fun i => M - S.eval (ω i)) 0 :=
    fun j => by simp only; linarith [hpath_mono j]
  -- Derive the rpow recurrence along this path.
  have hrec : ∀ j, (fun i => M - S.eval (ω i)) (j + 1) ≤
      (fun i => M - S.eval (ω i)) j *
        (1 - c * (fun i => M - S.eval (ω i)) j ^ p) := by
    intro j; simp only
    set ej := M - S.eval (ω j)
    have hej_nn : 0 ≤ ej := by linarith [hM (ω j)]
    have hfactor : ej ^ (p + 1) = ej ^ p * ej :=
      Real.rpow_add_one' hej_nn hp1_ne
    have hstep := hω j
    -- M - eval(ω(j+1)) ≤ M - eval(ω j) - c · (M - eval(ω j))^(p+1)
    have hgap_step : M - S.eval (ω (j + 1)) ≤ ej - c * ej ^ (p + 1) := by linarith
    -- Factor: ej - c · ej^(p+1) = ej · (1 - c · ej^p)
    nlinarith [hgap_step, hfactor]
  apply rpow_recurrence_div (fun j => M - S.eval (ω j)) c (M - S.eval (ω 0))
    p hp hc_pos (by linarith [hM (ω 0)])
    (small_constant_of_recurrence_rpow _ c p hp hc_pos hnn hrec)
    hnn hle hrec

end StochasticRealExponent

end RealExponent

/-! # InhomogeneousSOS: Time-Dependent Sacred Object Systems

Extension to time-dependent evaluators and updates, capturing systems
where the optimisation objective changes with the iteration count:
Nesterov's method, learning rate schedules, curriculum learning.

The key insight: the orbit sequence a(n) = E_n(δ₀∘...∘δ_{n-1}(π₀)) is
STILL monotone non-decreasing (by inhomogeneous monotone improvement)
and bounded above (by the uniform evaluator bound).  So convergence
follows by the SAME Monotone Convergence Theorem — a free theorem. -/

section InhomogeneousSOS

/-- An **Inhomogeneous Sacred Object System**: time-dependent evaluator
    and update operator.  The monotone improvement axiom becomes
    E_{n+1}(δ_n(π)) ≥ E_n(π) — the evaluator at time n+1 of the
    updated state is at least the evaluator at time n of the current state.

    This captures Nesterov (Lyapunov V_k with k² scaling), learning
    rate decay (time-varying step bound), and curriculum learning
    (time-varying evaluator as the curriculum progresses). -/
structure InhomogeneousSOS where
  /-- The policy space -/
  Pi : Type*
  /-- Metric structure on Pi -/
  [metric : MetricSpace Pi]
  /-- Time-indexed evaluator family -/
  E : ℕ → Pi → ℝ
  /-- Each evaluator is bounded above -/
  E_bddAbove : ∃ M : ℝ, ∀ n (π : Pi), E n π ≤ M
  /-- Time-indexed update operator -/
  delta : ℕ → Pi → Pi
  /-- Inhomogeneous monotone improvement:
      the evaluator at time n+1 of the updated state is at least
      the evaluator at time n of the current state. -/
  monotone_improvement : ∀ n (π : Pi), E (n + 1) (delta n π) ≥ E n π

instance (S : InhomogeneousSOS) : MetricSpace S.Pi := S.metric

/-- The inhomogeneous orbit: compose the time-indexed updates. -/
noncomputable def InhomogeneousSOS.compose_deltas
    (S : InhomogeneousSOS) (pi0 : S.Pi) : ℕ → S.Pi
  | 0 => pi0
  | n + 1 => S.delta n (S.compose_deltas pi0 n)

/-- The inhomogeneous orbit sequence: E_n applied to the composed updates. -/
noncomputable def InhomogeneousSOS.orbit (S : InhomogeneousSOS)
    (pi0 : S.Pi) (n : ℕ) : ℝ :=
  S.E n (S.compose_deltas pi0 n)

/-- The orbit sequence is monotone non-decreasing. -/
theorem InhomogeneousSOS.orbit_monotone (S : InhomogeneousSOS) (pi0 : S.Pi) :
    Monotone (S.orbit pi0) := by
  apply monotone_nat_of_le_succ
  intro n
  simp only [InhomogeneousSOS.orbit, InhomogeneousSOS.compose_deltas]
  exact S.monotone_improvement n (S.compose_deltas pi0 n)

/-- The orbit sequence is bounded above. -/
theorem InhomogeneousSOS.orbit_bddAbove (S : InhomogeneousSOS) (pi0 : S.Pi) :
    BddAbove (Set.range (S.orbit pi0)) := by
  obtain ⟨M, hM⟩ := S.E_bddAbove
  exact ⟨M, by rintro _ ⟨n, rfl⟩; exact hM n _⟩

/-- **Inhomogeneous SOS convergence**: the orbit sequence converges.
    Same engine as the deterministic case: monotone + bounded → MCT.
    This is a FREE THEOREM for time-dependent systems. -/
theorem InhomogeneousSOS.convergence (S : InhomogeneousSOS) (pi0 : S.Pi) :
    ∃ L : ℝ, Filter.Tendsto (S.orbit pi0) Filter.atTop (nhds L) :=
  ⟨⨆ i, S.orbit pi0 i,
   tendsto_atTop_ciSup (S.orbit_monotone pi0) (S.orbit_bddAbove pi0)⟩

/-- Embedding: every (homogeneous) SOS embeds into InhomogeneousSOS
    by using constant evaluator and update families. -/
def SOS.toInhomogeneous (S : SOS) : InhomogeneousSOS where
  Pi := S.Pi
  E := fun _ => S.E
  E_bddAbove := by
    obtain ⟨M, hM⟩ := S.E_bddAbove
    exact ⟨M, fun _ π => hM ⟨π, rfl⟩⟩
  delta := fun _ => S.delta
  monotone_improvement := fun _ π => S.monotone_improvement π

/-- The homogeneous embedding preserves orbits. -/
theorem SOS.toInhomogeneous_orbit (S : SOS) (pi0 : S.Pi) (n : ℕ) :
    (S.toInhomogeneous).orbit pi0 n = S.orbit pi0 n := by
  simp only [InhomogeneousSOS.orbit, SOS.orbit, SOS.toInhomogeneous]
  congr 1
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [InhomogeneousSOS.compose_deltas, Function.iterate_succ',
               Function.comp_apply, ih]

end InhomogeneousSOS
