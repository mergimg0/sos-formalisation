/-
  Sacred Object System (SOS) — Complete Formalization (Phases 1–6)
  A general algebraic structure unifying iterative optimization systems
  (Autoresearch, PPO, ECEF) under common convergence guarantees.

  Phase 1: Core SOS structure definition
  Phase 2: Convergence theorem + orbit properties
  Phase 3: SOS morphisms and category structure
  Phase 4: Instantiation proofs (PPO axiom, Autoresearch + ECEF concrete)
  Phase 5: Lipschitz bounds (Spectral Normalization, Triple Safety)
  Phase 6: Policy space convergence (completeness + contraction)
-/

import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.CategoryTheory.Category.Basic

/-! # Phase 1: Core SOS Structure -/

/-- A Sacred Object System: a metric policy space with a bounded monotone
    evaluator, constraint predicate, and update operator. -/
structure SOS where
  /-- The mutable policy space -/
  Pi : Type*
  /-- Metric structure on Pi -/
  [metric : MetricSpace Pi]
  /-- The evaluator function -/
  E : Pi → ℝ
  /-- E is bounded above -/
  E_bddAbove : BddAbove (Set.range E)
  /-- Maximum step size -/
  Delta : ℝ
  /-- Delta is positive -/
  Delta_pos : Delta > 0
  /-- Constraint predicate -/
  C : Pi → Prop
  /-- The update operator -/
  delta : Pi → Pi
  /-- Axiom (i): Monotone improvement — each update does not decrease E -/
  monotone_improvement : ∀ (pi : Pi), E (delta pi) ≥ E pi
  /-- Axiom (ii): Bounded step — updates stay within Delta distance -/
  bounded_step : ∀ (pi : Pi), dist (delta pi) pi ≤ Delta
  /-- Axiom (iii): Constraint preservation — valid states remain valid -/
  constraint_preservation : ∀ (pi : Pi), C pi → C (delta pi)

/-- Register the metric instance so Lean can find it. -/
instance (S : SOS) : MetricSpace S.Pi := S.metric

/-! # Phase 2: Convergence Theorem -/

/-- The orbit sequence: E evaluated along iterated updates. -/
noncomputable def SOS.orbit (S : SOS) (pi0 : S.Pi) (n : ℕ) : ℝ :=
  S.E (S.delta^[n] pi0)

/-- Each step of the orbit is non-decreasing. -/
lemma SOS.orbit_le_succ (S : SOS) (pi0 : S.Pi) (n : ℕ) :
    S.orbit pi0 n ≤ S.orbit pi0 (n + 1) := by
  simp only [SOS.orbit, Function.iterate_succ', Function.comp_apply]
  exact S.monotone_improvement (S.delta^[n] pi0)

/-- The orbit sequence is monotone non-decreasing. -/
theorem SOS.orbit_monotone (S : SOS) (pi0 : S.Pi) :
    Monotone (S.orbit pi0) :=
  monotone_nat_of_le_succ (S.orbit_le_succ pi0)

/-- The orbit sequence is bounded above (inherits from E's bound). -/
theorem SOS.orbit_bddAbove (S : SOS) (pi0 : S.Pi) :
    BddAbove (Set.range (S.orbit pi0)) := by
  obtain ⟨M, hM⟩ := S.E_bddAbove
  exact ⟨M, by rintro _ ⟨n, rfl⟩; exact hM ⟨S.delta^[n] pi0, rfl⟩⟩

/-- **Main Theorem (Phase 2)**: For any SOS and initial policy, the evaluator
    sequence converges. This is the Monotone Convergence Theorem applied to
    the SOS orbit: the sequence is monotone non-decreasing and bounded above,
    therefore it converges to a limit. -/
theorem SOS.convergence (S : SOS) (pi0 : S.Pi) :
    ∃ L : ℝ, Filter.Tendsto (S.orbit pi0) Filter.atTop (nhds L) :=
  ⟨⨆ i, S.orbit pi0 i, tendsto_atTop_ciSup (S.orbit_monotone pi0) (S.orbit_bddAbove pi0)⟩

/-- Constraints are preserved along the entire orbit. -/
theorem SOS.constraint_along_orbit (S : SOS) (pi0 : S.Pi) (hC : S.C pi0) (n : ℕ) :
    S.C (S.delta^[n] pi0) := by
  induction n with
  | zero => exact hC
  | succ n ih =>
    simp only [Function.iterate_succ', Function.comp_apply]
    exact S.constraint_preservation _ ih

/-- The orbit stays within a bounded ball (uses bounded_step + triangle inequality). -/
theorem SOS.orbit_bounded (S : SOS) (pi0 : S.Pi) (n : ℕ) :
    dist (S.delta^[n] pi0) pi0 ≤ ↑n * S.Delta := by
  induction n with
  | zero => simp [dist_self]
  | succ n ih =>
    calc dist (S.delta^[n + 1] pi0) pi0
        ≤ dist (S.delta^[n + 1] pi0) (S.delta^[n] pi0)
          + dist (S.delta^[n] pi0) pi0 := dist_triangle _ _ _
      _ ≤ S.Delta + ↑n * S.Delta := by
          apply add_le_add
          · simp only [Function.iterate_succ', Function.comp_apply]
            exact S.bounded_step _
          · exact ih
      _ = ↑(n + 1) * S.Delta := by push_cast; ring

/-- Each orbit value is bounded by the supremum. -/
theorem SOS.orbit_le_limit (S : SOS) (pi0 : S.Pi) (n : ℕ) :
    S.orbit pi0 n ≤ ⨆ i, S.orbit pi0 i :=
  le_ciSup (S.orbit_bddAbove pi0) n

/-- **Improvement vanishes** (Phase A3): The per-step evaluator improvement
    E(δ^[n+1](π₀)) − E(δ^[n](π₀)) → 0 as n → ∞. The update operator produces
    diminishing returns. Proof: both orbit(n) and orbit(n+1) converge to L,
    so their difference converges to 0. -/
theorem SOS.improvement_vanishes (S : SOS) (pi0 : S.Pi)
    {L : ℝ} (hL : Filter.Tendsto (S.orbit pi0) Filter.atTop (nhds L)) :
    Filter.Tendsto (fun n => S.orbit pi0 (n + 1) - S.orbit pi0 n) Filter.atTop (nhds 0) := by
  have hshift : Filter.Tendsto (fun n => S.orbit pi0 (n + 1)) Filter.atTop (nhds L) :=
    hL.comp (Filter.tendsto_atTop_atTop_of_monotone
      (fun _ _ h => Nat.add_le_add_right h 1) fun b => ⟨b, Nat.le_add_right b 1⟩)
  rw [show (0 : ℝ) = L - L from (sub_self L).symm]
  exact Filter.Tendsto.sub hshift hL

/-! ## Constraint Lifting: General Construction

Given any SOS S and a predicate C, produce a new SOS with constraint C
by wrapping S's update: accept δ(π) iff C(δ(π)) holds, otherwise keep π.
Since S already guarantees E(δ(π)) ≥ E(π), only the constraint needs checking.
This shows the Constraint Preservation axiom supports modular composition:
any SOS can be given non-trivial constraints via a one-line construction. -/

open Classical in
/-- **Constraint Lifting**: wrap any SOS's update with a constraint check
    to produce an SOS with non-trivial constraint preservation. -/
noncomputable def SOS.constraintLift (S : SOS) (C : S.Pi → Prop) : SOS where
  Pi := S.Pi
  E := S.E
  E_bddAbove := S.E_bddAbove
  Delta := S.Delta
  Delta_pos := S.Delta_pos
  C := C
  delta := fun π => if C (S.delta π) then S.delta π else π
  monotone_improvement := fun π => by
    change S.E (if C (S.delta π) then S.delta π else π) ≥ S.E π
    split_ifs with h
    · exact S.monotone_improvement π
    · exact le_refl _
  bounded_step := fun π => by
    change dist (if C (S.delta π) then S.delta π else π) π ≤ S.Delta
    split_ifs with h
    · exact S.bounded_step π
    · rw [dist_self]; exact le_of_lt S.Delta_pos
  constraint_preservation := fun π hc => by
    change C (if C (S.delta π) then S.delta π else π)
    split_ifs with h
    · exact h
    · exact hc

/-- Constraint lifting preserves convergence: free theorem. -/
theorem SOS.constraintLift_convergence (S : SOS) (C : S.Pi → Prop) (π0 : S.Pi) :
    ∃ L : ℝ, Filter.Tendsto
      ((S.constraintLift C).orbit π0)
      Filter.atTop (nhds L) :=
  (S.constraintLift C).convergence π0

/-! ## Phase Transition: Switching Evaluators Mid-Training

When the evaluator changes from E₁ to E₂ at step k (e.g., ProofForge
binary → efficiency reward at step 50), the combined orbit is NOT covered
by the single-SOS convergence theorem because E changes mid-trajectory.

What IS provable:
1. Each segment individually converges (trivial from SOS.convergence).
2. The transition drop E₁(π_k) - E₂(π_k) is non-negative when E₂ ≤ E₁
   pointwise (efficiency reward is stricter than binary).
3. The combined orbit is piecewise monotone with at most one descent
   at the transition boundary.

What is NOT proven here (and cannot be without additional axioms):
- That L₂ ≥ L₁ (the second limit may be lower than the first).
- That the combined orbit converges in any global sense.

Paper language: "Piecewise convergence across evaluator transitions is
a consequence of the SOS framework (Theorem restarted_convergence).
The transition boundary has a bounded non-monotone step
(Theorem evaluator_drop_nonneg)." -/

/-- **Restarted Convergence**: any SOS converges from any starting point,
    including a policy obtained as the k-th iterate of a different SOS.
    This is a direct corollary of SOS.convergence applied to the
    transition starting point π_k = δ₁^[k](π₀). -/
theorem SOS.restarted_convergence
    (S₁ S₂ : SOS)
    (h_same_Pi : S₁.Pi = S₂.Pi)
    (π₀ : S₁.Pi) (k : ℕ) :
    ∃ L₂ : ℝ, Filter.Tendsto
      (S₂.orbit (h_same_Pi ▸ (S₁.delta^[k] π₀)))
      Filter.atTop (nhds L₂) :=
  S₂.convergence (h_same_Pi ▸ (S₁.delta^[k] π₀))

/-- **Evaluator Drop Bound**: when the new evaluator E₂ is pointwise
    ≤ the old evaluator E₁ (efficiency reward ≤ binary reward for all
    policies), the one-step drop at the transition is non-negative.
    This bounds the non-monotone step: the orbit can decrease by at most
    E₁(π) - E₂(π) at the transition. -/
theorem SOS.evaluator_drop_nonneg
    (S₁ S₂ : SOS)
    (h_same_Pi : S₁.Pi = S₂.Pi)
    (h_stricter : ∀ (π : S₁.Pi), S₂.E (h_same_Pi ▸ π) ≤ S₁.E π)
    (π : S₁.Pi) :
    0 ≤ S₁.E π - S₂.E (h_same_Pi ▸ π) :=
  sub_nonneg.mpr (h_stricter π)

/-- **Piecewise Convergence**: each segment of a two-phase training run
    converges independently. A direct consequence of SOS.convergence
    applied twice. -/
theorem SOS.piecewise_convergence
    (S₁ S₂ : SOS)
    (h_same_Pi : S₁.Pi = S₂.Pi)
    (π₀ : S₁.Pi) :
    (∃ L₁, Filter.Tendsto (S₁.orbit π₀) Filter.atTop (nhds L₁)) ∧
    (∀ k, ∃ L₂, Filter.Tendsto
      (S₂.orbit (h_same_Pi ▸ (S₁.delta^[k] π₀)))
      Filter.atTop (nhds L₂)) :=
  ⟨S₁.convergence π₀, fun _ => S₂.convergence _⟩

/-! ## Geometric Convergence Rate under Łojasiewicz Condition

If each update step captures at least a fixed fraction c of the remaining
gap to an upper bound M, the orbit converges geometrically: the gap decays
as (1-c)^n.  This is the quantitative counterpart of the qualitative
convergence theorem.  The condition E(δ(π)) - E(π) ≥ c·(M - E(π)) is
satisfied by algorithms with unique optima under convexity/concavity:
exact PI on finite MDPs, EM on strongly log-concave models, gradient
descent on strongly convex functions. -/

/-- **Geometric convergence rate**: under a Łojasiewicz condition
    E(δ(π)) - E(π) ≥ c · (M - E(π)), the gap to M decays as (1-c)^n. -/
theorem SOS.geometric_rate (S : SOS) (pi0 : S.Pi)
    {M : ℝ} (hM : ∀ π : S.Pi, S.E π ≤ M)
    {c : ℝ} (hc_le : c ≤ 1)
    (hLoj : ∀ π : S.Pi, S.E (S.delta π) - S.E π ≥ c * (M - S.E π))
    (n : ℕ) :
    M - S.orbit pi0 n ≤ (1 - c) ^ n * (M - S.E pi0) := by
  induction n with
  | zero =>
    simp only [SOS.orbit, Function.iterate_zero, id_eq, pow_zero, one_mul]
    exact le_refl _
  | succ n ih =>
    simp only [SOS.orbit, Function.iterate_succ', Function.comp_apply]
    have step := hLoj (S.delta^[n] pi0)
    have hgap : M - S.E (S.delta^[n] pi0) ≥ 0 := by linarith [hM (S.delta^[n] pi0)]
    calc M - S.E (S.delta (S.delta^[n] pi0))
        ≤ M - S.E (S.delta^[n] pi0) - c * (M - S.E (S.delta^[n] pi0)) := by linarith
      _ = (1 - c) * (M - S.E (S.delta^[n] pi0)) := by ring
      _ ≤ (1 - c) * ((1 - c) ^ n * (M - S.E pi0)) := by
          apply mul_le_mul_of_nonneg_left ih; linarith
      _ = (1 - c) ^ (n + 1) * (M - S.E pi0) := by ring

/-! ## Local Convergence Rates

The global Łojasiewicz condition requires E(δ(π)) - E(π) ≥ c·(M - E(π))
for ALL π, which fails for algorithms converging to local optima
(EM on multimodal distributions, PPO in practice).  The local version
relativises to a δ-invariant subset (basin), replacing the global bound
M with a basin-specific upper bound M_B.  The proof structure is identical
to the global case; δ-invariance keeps δⁿ(π₀) ∈ B at every induction step. -/

/-- A **basin** is a δ-invariant subset: if π ∈ B then δ(π) ∈ B.
    Orbits starting in B remain in B forever. -/
def SOS.IsBasin (S : SOS) (B : Set S.Pi) : Prop :=
  ∀ π ∈ B, S.delta π ∈ B

/-- Iterated updates stay in a basin: if π₀ ∈ B and B is a basin,
    then δⁿ(π₀) ∈ B for all n. -/
theorem SOS.iterate_mem_basin (S : SOS) {B : Set S.Pi}
    (hB : S.IsBasin B) {pi0 : S.Pi} (h0 : pi0 ∈ B)
    (n : ℕ) : S.delta^[n] pi0 ∈ B := by
  induction n with
  | zero => exact h0
  | succ n ih =>
    rw [Function.iterate_succ', Function.comp_apply]
    exact hB _ ih

/-- The orbit of any point is itself a basin (trivially δ-invariant):
    {δⁿ(π₀) | n ∈ ℕ} is δ-invariant because δ(δⁿ(π₀)) = δⁿ⁺¹(π₀). -/
theorem SOS.orbit_is_basin (S : SOS) (pi0 : S.Pi) :
    S.IsBasin {π | ∃ n, S.delta^[n] pi0 = π} := by
  intro π ⟨n, hn⟩
  refine ⟨n + 1, ?_⟩
  simp only [Function.iterate_succ', Function.comp_apply, hn]

/-- **Local geometric convergence rate**: under a local Łojasiewicz
    condition on a basin B with bound M_B, the gap decays as (1-c_B)^n.
    Generalises `geometric_rate` by restricting to a δ-invariant subset. -/
theorem SOS.local_geometric_rate (S : SOS) (pi0 : S.Pi)
    {B : Set S.Pi} (hB : S.IsBasin B) (h0 : pi0 ∈ B)
    {M : ℝ} (hM : ∀ π ∈ B, S.E π ≤ M)
    {c : ℝ} (hc_le : c ≤ 1)
    (hLoj : ∀ π ∈ B, S.E (S.delta π) - S.E π ≥ c * (M - S.E π))
    (n : ℕ) :
    M - S.orbit pi0 n ≤ (1 - c) ^ n * (M - S.E pi0) := by
  induction n with
  | zero =>
    simp only [SOS.orbit, Function.iterate_zero, id_eq, pow_zero, one_mul]
    exact le_refl _
  | succ n ih =>
    simp only [SOS.orbit, Function.iterate_succ', Function.comp_apply]
    have hmem : S.delta^[n] pi0 ∈ B := S.iterate_mem_basin hB h0 n
    have step := hLoj _ hmem
    have hgap : M - S.E (S.delta^[n] pi0) ≥ 0 := by linarith [hM _ hmem]
    calc M - S.E (S.delta (S.delta^[n] pi0))
        ≤ M - S.E (S.delta^[n] pi0) - c * (M - S.E (S.delta^[n] pi0)) := by linarith
      _ = (1 - c) * (M - S.E (S.delta^[n] pi0)) := by ring
      _ ≤ (1 - c) * ((1 - c) ^ n * (M - S.E pi0)) := by
          apply mul_le_mul_of_nonneg_left ih; linarith
      _ = (1 - c) ^ (n + 1) * (M - S.E pi0) := by ring

/-- The global Łojasiewicz condition is the special case B = Set.univ.
    This shows that `local_geometric_rate` subsumes `geometric_rate`. -/
theorem SOS.geometric_rate_of_local (S : SOS) (pi0 : S.Pi)
    {M : ℝ} (hM : ∀ π : S.Pi, S.E π ≤ M)
    {c : ℝ} (hc_le : c ≤ 1)
    (hLoj : ∀ π : S.Pi, S.E (S.delta π) - S.E π ≥ c * (M - S.E π))
    (n : ℕ) :
    M - S.orbit pi0 n ≤ (1 - c) ^ n * (M - S.E pi0) :=
  S.local_geometric_rate pi0 (B := Set.univ)
    (fun _ _ => Set.mem_univ _) (Set.mem_univ _)
    (fun π _ => hM π) hc_le (fun π _ => hLoj π) n

/-! # Phase 3: SOS Morphisms and Category Structure -/

/-- A morphism between two Sacred Object Systems: a pair of maps (f, g) where
    f acts on policy spaces and g acts on evaluator values, preserving the
    SOS structure (evaluator compatibility, update commutativity, constraints). -/
structure SOS.Morphism (S1 S2 : SOS) where
  /-- Map on policy spaces -/
  f : S1.Pi → S2.Pi
  /-- Map on evaluator values -/
  g : ℝ → ℝ
  /-- g is monotone -/
  g_monotone : Monotone g
  /-- Evaluator compatibility: the diagram commutes -/
  evaluator_compat : ∀ (pi : S1.Pi), g (S1.E pi) = S2.E (f pi)
  /-- Update commutativity: f intertwines the update operators -/
  update_commute : ∀ (pi : S1.Pi), f (S1.delta pi) = S2.delta (f pi)
  /-- Constraint compatibility -/
  constraint_compat : ∀ (pi : S1.Pi), S1.C pi ↔ S2.C (f pi)

/-- Identity morphism. -/
def SOS.Morphism.id (S : SOS) : SOS.Morphism S S where
  f := _root_.id
  g := _root_.id
  g_monotone := monotone_id
  evaluator_compat := fun _ => rfl
  update_commute := fun _ => rfl
  constraint_compat := fun _ => Iff.rfl

/-- Composition of morphisms (categorical composition, right-to-left). -/
def SOS.Morphism.comp {S1 S2 S3 : SOS}
    (phi : SOS.Morphism S2 S3) (psi : SOS.Morphism S1 S2) :
    SOS.Morphism S1 S3 where
  f := phi.f ∘ psi.f
  g := phi.g ∘ psi.g
  g_monotone := phi.g_monotone.comp psi.g_monotone
  evaluator_compat := by
    intro pi
    simp only [Function.comp_apply]
    rw [psi.evaluator_compat, phi.evaluator_compat]
  update_commute := by
    intro pi
    simp only [Function.comp_apply]
    rw [psi.update_commute, phi.update_commute]
  constraint_compat := by
    intro pi
    exact (psi.constraint_compat pi).trans (phi.constraint_compat (psi.f pi))

/-- A morphism intertwines iterated updates: φ.f commutes with δ^[n]. -/
lemma SOS.Morphism.iterate_commute {S1 S2 : SOS}
    (phi : SOS.Morphism S1 S2) (pi : S1.Pi) (n : ℕ) :
    phi.f (S1.delta^[n] pi) = S2.delta^[n] (phi.f pi) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [Function.iterate_succ', Function.comp_apply]
    rw [phi.update_commute, ih]

/-- The orbit of a morphism's image equals g applied to the source orbit:
    S₂.orbit(φ.f(π₀), n) = φ.g(S₁.orbit(π₀, n)). -/
lemma SOS.Morphism.orbit_eq {S1 S2 : SOS}
    (phi : SOS.Morphism S1 S2) (pi0 : S1.Pi) (n : ℕ) :
    S2.orbit (phi.f pi0) n = phi.g (S1.orbit pi0 n) := by
  simp only [SOS.orbit]
  rw [← phi.iterate_commute, ← phi.evaluator_compat]

/-- **Orbit limit bound** (monotonicity only, no continuity):
    The limit of S₂'s orbit is bounded above by φ.g(L).
    This uses only that φ.g is monotone — no continuity needed.
    A strict gap ⨆ n, S₂.orbit(φ.f(π₀), n) < φ.g(L) is possible iff
    φ.g has a left discontinuity at L (the orbit approaches from below).
    For monotone g on ℝ, such discontinuities are countable. -/
theorem SOS.Morphism.limit_bound {S1 S2 : SOS}
    (phi : SOS.Morphism S1 S2) (pi0 : S1.Pi)
    {L : ℝ} (hL : Filter.Tendsto (S1.orbit pi0) Filter.atTop (nhds L)) :
    ⨆ n, S2.orbit (phi.f pi0) n ≤ phi.g L := by
  have hL_sup : L = ⨆ n, S1.orbit pi0 n :=
    tendsto_nhds_unique hL
      (tendsto_atTop_ciSup (S1.orbit_monotone pi0) (S1.orbit_bddAbove pi0))
  apply ciSup_le
  intro n
  rw [phi.orbit_eq pi0 n, hL_sup]
  exact phi.g_monotone (le_ciSup (S1.orbit_bddAbove pi0) n)

/-- **Strong convergence preservation** (requires continuity of φ.g):
    If φ.g is continuous and S₁'s orbit converges to L, then S₂'s orbit
    converges to exactly φ.g(L). This is the full limit-transfer theorem. -/
theorem SOS.Morphism.preserves_convergence_limit {S1 S2 : SOS}
    (phi : SOS.Morphism S1 S2) (pi0 : S1.Pi)
    (hg_cont : Continuous phi.g)
    {L : ℝ} (hL : Filter.Tendsto (S1.orbit pi0) Filter.atTop (nhds L)) :
    Filter.Tendsto (S2.orbit (phi.f pi0)) Filter.atTop (nhds (phi.g L)) := by
  have orbit_fn : S2.orbit (phi.f pi0) = phi.g ∘ S1.orbit pi0 := by
    ext n; exact phi.orbit_eq pi0 n
  rw [orbit_fn]
  exact (hg_cont.tendsto L).comp hL

/-- Extensionality for morphisms: two morphisms are equal if their f and g agree. -/
theorem SOS.Morphism.ext' {S1 S2 : SOS}
    {phi psi : SOS.Morphism S1 S2}
    (hf : phi.f = psi.f) (hg : phi.g = psi.g) :
    phi = psi := by
  cases phi; cases psi
  simp only [SOS.Morphism.mk.injEq]
  exact ⟨hf, hg⟩

/-- Left identity: id ∘ φ = φ. -/
theorem SOS.Morphism.id_comp {S1 S2 : SOS} (phi : SOS.Morphism S1 S2) :
    (SOS.Morphism.id S2).comp phi = phi :=
  SOS.Morphism.ext' rfl rfl

/-- Right identity: φ ∘ id = φ. -/
theorem SOS.Morphism.comp_id {S1 S2 : SOS} (phi : SOS.Morphism S1 S2) :
    phi.comp (SOS.Morphism.id S1) = phi :=
  SOS.Morphism.ext' rfl rfl

/-- Associativity: (φ ∘ ψ) ∘ χ = φ ∘ (ψ ∘ χ). -/
theorem SOS.Morphism.comp_assoc {S1 S2 S3 S4 : SOS}
    (phi : SOS.Morphism S3 S4) (psi : SOS.Morphism S2 S3)
    (chi : SOS.Morphism S1 S2) :
    (phi.comp psi).comp chi = phi.comp (psi.comp chi) :=
  SOS.Morphism.ext' rfl rfl

-- **Category instance**: SOS forms a category with objects = sacred object systems and
-- morphisms = SOS.Morphism.  Composition is diagrammatic (f ≫ g = g.comp f) since
-- Mathlib uses left-to-right arrows while our comp is right-to-left.
open CategoryTheory in
instance : LargeCategory SOS where
  Hom := SOS.Morphism
  id := SOS.Morphism.id
  comp f g := g.comp f
  id_comp f := f.comp_id
  comp_id f := f.id_comp
  assoc f g h := (SOS.Morphism.comp_assoc h g f).symm

/-- **Limit compatibility**: Under continuous φ.g, the supremum transfers exactly:
    ⨆ n, S₂.orbit(φ.f(π₀), n) = φ.g(⨆ n, S₁.orbit(π₀, n)). -/
theorem SOS.Morphism.limit_compat {S1 S2 : SOS}
    (phi : SOS.Morphism S1 S2) (pi0 : S1.Pi)
    (hg_cont : Continuous phi.g) :
    ⨆ n, S2.orbit (phi.f pi0) n = phi.g (⨆ n, S1.orbit pi0 n) := by
  have hL1 := tendsto_atTop_ciSup (S1.orbit_monotone pi0) (S1.orbit_bddAbove pi0)
  have hL2 := phi.preserves_convergence_limit pi0 hg_cont hL1
  have hL2' := tendsto_atTop_ciSup (S2.orbit_monotone (phi.f pi0)) (S2.orbit_bddAbove (phi.f pi0))
  exact tendsto_nhds_unique hL2' hL2

/-- **Rate transfer through Lipschitz morphisms**: if φ : S₁ → S₂ has
    g being K-Lipschitz (i.e., g(y) - g(x) ≤ K·(y-x) for all x ≤ y),
    and S₁ has geometric rate c w.r.t. upper bound M, then the image
    orbit in S₂ converges geometrically with the same rate and constant
    scaled by K.  This is the quantitative analogue of
    preserves_convergence_limit. -/
theorem SOS.Morphism.rate_transfer {S1 S2 : SOS}
    (phi : SOS.Morphism S1 S2) (pi0 : S1.Pi)
    {M : ℝ} (hM : ∀ π : S1.Pi, S1.E π ≤ M)
    {c : ℝ} (hc_le : c ≤ 1)
    (hLoj : ∀ π : S1.Pi, S1.E (S1.delta π) - S1.E π ≥ c * (M - S1.E π))
    {K : ℝ} (hK_pos : 0 ≤ K)
    (hg_lip : ∀ x y : ℝ, x ≤ y → phi.g y - phi.g x ≤ K * (y - x))
    (n : ℕ) :
    phi.g M - S2.orbit (phi.f pi0) n ≤
    K * ((1 - c) ^ n * (M - S1.E pi0)) := by
  rw [phi.orbit_eq pi0 n]
  simp only [SOS.orbit]
  -- Goal: phi.g M - phi.g (S1.E (S1.delta^[n] pi0)) ≤ K * ((1-c)^n * (M - S1.E pi0))
  have hlip := hg_lip (S1.E (S1.delta^[n] pi0)) M (hM (S1.delta^[n] pi0))
  -- hlip : phi.g M - phi.g (S1.E ...) ≤ K * (M - S1.E ...)
  have hrate := S1.geometric_rate pi0 hM hc_le hLoj n
  simp only [SOS.orbit] at hrate
  -- hrate : M - S1.E (S1.delta^[n] pi0) ≤ (1-c)^n * (M - S1.E pi0)
  calc phi.g M - phi.g (S1.E (S1.delta^[n] pi0))
      ≤ K * (M - S1.E (S1.delta^[n] pi0)) := hlip
    _ ≤ K * ((1 - c) ^ n * (M - S1.E pi0)) := by
        apply mul_le_mul_of_nonneg_left hrate hK_pos

/-- **Local rate transfer through Lipschitz morphisms**: if φ : S₁ → S₂
    has g K-Lipschitz, and S₁ satisfies a local Łojasiewicz condition on
    basin B, then the image orbit converges at the same geometric rate
    scaled by K.  Generalises `rate_transfer` to basins. -/
theorem SOS.Morphism.local_rate_transfer {S1 S2 : SOS}
    (phi : SOS.Morphism S1 S2) (pi0 : S1.Pi)
    {B : Set S1.Pi} (hB : S1.IsBasin B) (h0 : pi0 ∈ B)
    {M : ℝ} (hM : ∀ π ∈ B, S1.E π ≤ M)
    {c : ℝ} (hc_le : c ≤ 1)
    (hLoj : ∀ π ∈ B, S1.E (S1.delta π) - S1.E π ≥ c * (M - S1.E π))
    {K : ℝ} (hK_pos : 0 ≤ K)
    (hg_lip : ∀ x y : ℝ, x ≤ y → phi.g y - phi.g x ≤ K * (y - x))
    (n : ℕ) :
    phi.g M - S2.orbit (phi.f pi0) n ≤
    K * ((1 - c) ^ n * (M - S1.E pi0)) := by
  rw [phi.orbit_eq pi0 n]
  simp only [SOS.orbit]
  have hlip := hg_lip (S1.E (S1.delta^[n] pi0)) M
    (hM _ (S1.iterate_mem_basin hB h0 n))
  have hrate := S1.local_geometric_rate pi0 hB h0 hM hc_le hLoj n
  simp only [SOS.orbit] at hrate
  calc phi.g M - phi.g (S1.E (S1.delta^[n] pi0))
      ≤ K * (M - S1.E (S1.delta^[n] pi0)) := hlip
    _ ≤ K * ((1 - c) ^ n * (M - S1.E pi0)) := by
        apply mul_le_mul_of_nonneg_left hrate hK_pos

/-! ## Lax Morphisms

A lax morphism relaxes the strict update commutativity condition
f(δ₁(π)) = δ₂(f(π)) to an evaluator-level inequality:
E₂(f(δ₁(π))) ≥ E₂(δ₂(f(π))).  This says that the source dynamics,
viewed through the morphism, are "at least as good" as the target dynamics.
Every strict morphism is lax (the inequality holds as equality).

Evaluator compatibility is kept exact — only the update condition is relaxed.
This ensures composition works via the monotonicity of g:
  E₃(f₂(f₁(δ₁(π)))) = g₂(E₂(f₁(δ₁(π))))   ≥ g₂(E₂(δ₂(f₁(π))))
                      = E₃(f₂(δ₂(f₁(π))))   ≥ E₃(δ₃(f₂(f₁(π))))

Constraint compatibility is weakened from biconditional (↔) to implication (→):
lax morphisms preserve constraints forward but do not require the converse.

Lax morphisms form a category SOS_lax; strict morphisms embed as a wide
subcategory SOS ↪ SOS_lax via a functorial embedding that preserves identity
and composition. -/

/-- A lax morphism between SOS instances: evaluator compatibility is exact,
    but update commutativity is relaxed to an evaluator-level inequality.
    The constraint condition is weakened from ↔ to →. -/
structure SOS.LaxMorphism (S1 S2 : SOS) where
  /-- Map on policy spaces -/
  f : S1.Pi → S2.Pi
  /-- Map on evaluator values -/
  g : ℝ → ℝ
  /-- g is monotone -/
  g_monotone : Monotone g
  /-- Evaluator compatibility (exact): the diagram commutes -/
  evaluator_compat : ∀ (pi : S1.Pi), g (S1.E pi) = S2.E (f pi)
  /-- Lax update: source dynamics are at least as good as target dynamics
      through the morphism lens.  Replaces f(δ₁(π)) = δ₂(f(π)). -/
  lax_update : ∀ (pi : S1.Pi),
    S2.E (f (S1.delta pi)) ≥ S2.E (S2.delta (f pi))
  /-- Constraint compatibility (forward only) -/
  constraint_compat : ∀ (pi : S1.Pi), S1.C pi → S2.C (f pi)

/-- Extensionality for lax morphisms: two lax morphisms with the same
    underlying maps are equal (proof fields are propositions). -/
theorem SOS.LaxMorphism.ext' {S1 S2 : SOS}
    {phi psi : SOS.LaxMorphism S1 S2}
    (hf : phi.f = psi.f) (hg : phi.g = psi.g) :
    phi = psi := by
  cases phi; cases psi
  simp only [SOS.LaxMorphism.mk.injEq]
  exact ⟨hf, hg⟩

/-- Identity lax morphism. -/
def SOS.LaxMorphism.id (S : SOS) : SOS.LaxMorphism S S where
  f := _root_.id
  g := _root_.id
  g_monotone := monotone_id
  evaluator_compat := fun _ => rfl
  lax_update := fun _ => le_refl _
  constraint_compat := fun _ h => h

/-- Composition of lax morphisms.  The lax update for the composite is
    established by the chain inequality:
      E₃(f₂(f₁(δ₁(π))))  = g₂(E₂(f₁(δ₁(π))))    [eval compat]
                           ≥ g₂(E₂(δ₂(f₁(π))))    [g₂ mono + φ₁ lax]
                           = E₃(f₂(δ₂(f₁(π))))    [eval compat]
                           ≥ E₃(δ₃(f₂(f₁(π))))    [φ₂ lax]
    The two ≥ steps use different morphisms; the two = steps both use
    evaluator compatibility of φ₂ at different arguments. -/
def SOS.LaxMorphism.comp {S1 S2 S3 : SOS}
    (phi : SOS.LaxMorphism S2 S3) (psi : SOS.LaxMorphism S1 S2) :
    SOS.LaxMorphism S1 S3 where
  f := phi.f ∘ psi.f
  g := phi.g ∘ psi.g
  g_monotone := phi.g_monotone.comp psi.g_monotone
  evaluator_compat := by
    intro pi; simp only [Function.comp_apply]
    rw [psi.evaluator_compat, phi.evaluator_compat]
  lax_update := fun pi => by
    simp only [Function.comp_apply]
    -- Chain: δ₃(f₂(f₁(π))) ≤ f₂(δ₂(f₁(π))) ≤ f₂(f₁(δ₁(π))) at evaluator level
    have h1 : S3.E (S3.delta (phi.f (psi.f pi))) ≤
        S3.E (phi.f (S2.delta (psi.f pi))) := phi.lax_update (psi.f pi)
    have h2 : S3.E (phi.f (S2.delta (psi.f pi))) ≤
        S3.E (phi.f (psi.f (S1.delta pi))) := by
      simp only [← phi.evaluator_compat]
      exact phi.g_monotone (psi.lax_update pi)
    exact h1.trans h2
  constraint_compat := fun pi h => phi.constraint_compat _ (psi.constraint_compat pi h)

/-- Left identity: id ∘ φ = φ. -/
theorem SOS.LaxMorphism.id_comp {S1 S2 : SOS} (phi : SOS.LaxMorphism S1 S2) :
    (SOS.LaxMorphism.id S2).comp phi = phi :=
  SOS.LaxMorphism.ext' rfl rfl

/-- Right identity: φ ∘ id = φ. -/
theorem SOS.LaxMorphism.comp_id {S1 S2 : SOS} (phi : SOS.LaxMorphism S1 S2) :
    phi.comp (SOS.LaxMorphism.id S1) = phi :=
  SOS.LaxMorphism.ext' rfl rfl

/-- Associativity: (φ ∘ ψ) ∘ χ = φ ∘ (ψ ∘ χ). -/
theorem SOS.LaxMorphism.comp_assoc {S1 S2 S3 S4 : SOS}
    (phi : SOS.LaxMorphism S3 S4) (psi : SOS.LaxMorphism S2 S3)
    (chi : SOS.LaxMorphism S1 S2) :
    (phi.comp psi).comp chi = phi.comp (psi.comp chi) :=
  SOS.LaxMorphism.ext' rfl rfl

/-- Every strict morphism embeds as a lax morphism.  The lax update
    follows from strict update commutativity: f(δ₁(π)) = δ₂(f(π)) implies
    E₂(f(δ₁(π))) = E₂(δ₂(f(π))) ≥ E₂(δ₂(f(π))). -/
def SOS.Morphism.toLaxMorphism {S1 S2 : SOS} (phi : SOS.Morphism S1 S2) :
    SOS.LaxMorphism S1 S2 where
  f := phi.f
  g := phi.g
  g_monotone := phi.g_monotone
  evaluator_compat := phi.evaluator_compat
  lax_update := fun pi => by rw [phi.update_commute]
  constraint_compat := fun pi => (phi.constraint_compat pi).mp

/-- The embedding preserves composition: toLaxMorphism is functorial.
    (φ ∘ ψ).toLax = φ.toLax ∘ ψ.toLax -/
theorem SOS.Morphism.toLaxMorphism_comp {S1 S2 S3 : SOS}
    (phi : SOS.Morphism S2 S3) (psi : SOS.Morphism S1 S2) :
    (phi.comp psi).toLaxMorphism = phi.toLaxMorphism.comp psi.toLaxMorphism :=
  SOS.LaxMorphism.ext' rfl rfl

/-- The embedding preserves identity: id.toLax = id_lax. -/
theorem SOS.Morphism.toLaxMorphism_id (S : SOS) :
    (SOS.Morphism.id S).toLaxMorphism = SOS.LaxMorphism.id S :=
  SOS.LaxMorphism.ext' rfl rfl

/-- **Lax image convergence**: the sequence E₂(f(δ₁ⁿ(π₀))) converges
    to g(L) whenever S₁'s orbit converges to L.
    Note: this converges to g(L), not to the limit of S₂'s own orbit.
    The relationship to S₂'s actual iterates δ₂ⁿ(f(π₀)) is lost in the
    lax setting — this is the fundamental tradeoff vs strict morphisms. -/
theorem SOS.LaxMorphism.lax_image_convergence {S1 S2 : SOS}
    (phi : SOS.LaxMorphism S1 S2) (pi0 : S1.Pi)
    (hg_cont : Continuous phi.g)
    {L : ℝ} (hL : Filter.Tendsto (S1.orbit pi0) Filter.atTop (nhds L)) :
    Filter.Tendsto (fun n => S2.E (phi.f (S1.delta^[n] pi0)))
      Filter.atTop (nhds (phi.g L)) := by
  have heq : (fun n => S2.E (phi.f (S1.delta^[n] pi0))) = phi.g ∘ S1.orbit pi0 := by
    ext n; simp only [SOS.orbit, Function.comp_apply, ← phi.evaluator_compat]
  rw [heq]
  exact (hg_cont.tendsto L).comp hL

/-- **Lax limit bound**: the supremum of the image evaluator sequence
    is bounded by g(L). -/
theorem SOS.LaxMorphism.lax_limit_bound {S1 S2 : SOS}
    (phi : SOS.LaxMorphism S1 S2) (pi0 : S1.Pi)
    {L : ℝ} (hL : Filter.Tendsto (S1.orbit pi0) Filter.atTop (nhds L)) :
    ⨆ n, S2.E (phi.f (S1.delta^[n] pi0)) ≤ phi.g L := by
  have hL_sup : L = ⨆ n, S1.orbit pi0 n :=
    tendsto_nhds_unique hL
      (tendsto_atTop_ciSup (S1.orbit_monotone pi0) (S1.orbit_bddAbove pi0))
  apply ciSup_le; intro n
  have : S2.E (phi.f (S1.delta^[n] pi0)) = phi.g (S1.orbit pi0 n) := by
    unfold SOS.orbit; rw [← phi.evaluator_compat]
  rw [this, hL_sup]
  exact phi.g_monotone (le_ciSup (S1.orbit_bddAbove pi0) n)

/-! # Phase 4: Instantiation Proofs

PPO is axiomatized (trust region theory requires deep RL formalization).
Autoresearch and ECEF are **constructed concretely** — no axioms needed. -/

/-- **PPO as SOS**: Proximal Policy Optimization. Axiomatized because proving
    monotone improvement requires formalizing the clipped surrogate objective
    and trust region guarantee (Schulman et al., 2017). -/
axiom PPO_is_SOS : SOS

/-- PPO convergence: immediate corollary of the SOS convergence theorem. -/
theorem PPO_convergence (pi0 : PPO_is_SOS.Pi) :
    ∃ L : ℝ, Filter.Tendsto (PPO_is_SOS.orbit pi0) Filter.atTop (nhds L) :=
  PPO_is_SOS.convergence pi0

/-! ## Autoresearch: Concrete Construction

The keep/discard mechanism is the key to monotone improvement.
At each step: propose a modification, evaluate it, keep only if it improves E.
This makes E(δ(π)) = max(E(proposed), E(π)) ≥ E(π) — monotonicity is trivial. -/

section Autoresearch
variable {Arch : Type*} [MetricSpace Arch]

open Classical in
/-- The keep/discard update: accept the proposal iff it improves E. -/
noncomputable def keepDiscard (E : Arch → ℝ) (propose : Arch → Arch) (a : Arch) : Arch :=
  if E (propose a) ≥ E a then propose a else a

omit [MetricSpace Arch] in
/-- Keep/discard never decreases E: E(keepDiscard(a)) ≥ E(a). -/
theorem keepDiscard_monotone_improvement (E : Arch → ℝ) (propose : Arch → Arch) (a : Arch) :
    E (keepDiscard E propose a) ≥ E a := by
  unfold keepDiscard
  split_ifs with h
  · exact h
  · exact le_refl _

/-- Keep/discard step is bounded by the proposal step (discarding = zero distance). -/
theorem keepDiscard_bounded (E : Arch → ℝ) (propose : Arch → Arch) (a : Arch) :
    dist (keepDiscard E propose a) a ≤ dist (propose a) a := by
  unfold keepDiscard
  split_ifs
  · exact le_refl _
  · rw [dist_self]; exact dist_nonneg

open Classical in
/-- **Autoresearch as a concrete SOS** (Phase B1): No axioms needed.
    The keep/discard mechanism directly satisfies all three SOS axioms:
    (i) Monotone improvement from keepDiscard_monotone_improvement
    (ii) Bounded step from keepDiscard_bounded + proposal boundedness
    (iii) Constraints trivially True (no constraints in basic autoresearch) -/
noncomputable def autoresearchSOS
    (E : Arch → ℝ) (propose : Arch → Arch)
    (hE_bdd : BddAbove (Set.range E))
    (D : ℝ) (hD : D > 0)
    (hPropose_bdd : ∀ a : Arch, dist (propose a) a ≤ D) : SOS where
  Pi := Arch
  E := E
  E_bddAbove := hE_bdd
  Delta := D
  Delta_pos := hD
  C := fun _ => True
  delta := keepDiscard E propose
  monotone_improvement := keepDiscard_monotone_improvement E propose
  bounded_step := fun a => (keepDiscard_bounded E propose a).trans (hPropose_bdd a)
  constraint_preservation := fun _ _ => trivial

/-- Autoresearch convergence: free theorem from the concrete construction. -/
theorem autoresearch_convergence
    (E : Arch → ℝ) (propose : Arch → Arch)
    (hE_bdd : BddAbove (Set.range E))
    (D : ℝ) (hD : D > 0)
    (hPropose_bdd : ∀ a : Arch, dist (propose a) a ≤ D)
    (pi0 : Arch) :
    ∃ L : ℝ, Filter.Tendsto
      ((autoresearchSOS E propose hE_bdd D hD hPropose_bdd).orbit pi0)
      Filter.atTop (nhds L) :=
  (autoresearchSOS E propose hE_bdd D hD hPropose_bdd).convergence pi0

end Autoresearch

/-! ## Constrained Autoresearch: Non-trivial Constraint Preservation

The constrained keep/discard mechanism checks both evaluator improvement AND
a constraint predicate before accepting a proposal. This demonstrates
the Constraint Preservation axiom on a non-trivial predicate. -/

section ConstrainedAutoresearch
variable {Arch : Type*} [MetricSpace Arch]

open Classical in
/-- Constrained keep/discard: accept proposal iff it improves E AND satisfies C. -/
noncomputable def constrainedKeepDiscard (E : Arch → ℝ) (propose : Arch → Arch)
    (C : Arch → Prop) (a : Arch) : Arch :=
  if E (propose a) ≥ E a ∧ C (propose a) then propose a else a

omit [MetricSpace Arch] in
/-- Constrained keep/discard never decreases E. -/
theorem constrainedKeepDiscard_monotone (E : Arch → ℝ) (propose : Arch → Arch)
    (C : Arch → Prop) (a : Arch) :
    E (constrainedKeepDiscard E propose C a) ≥ E a := by
  unfold constrainedKeepDiscard
  split_ifs with h
  · exact h.1
  · exact le_refl _

/-- Constrained keep/discard step is bounded by the proposal step. -/
theorem constrainedKeepDiscard_bounded (E : Arch → ℝ) (propose : Arch → Arch)
    (C : Arch → Prop) (a : Arch) :
    dist (constrainedKeepDiscard E propose C a) a ≤ dist (propose a) a := by
  unfold constrainedKeepDiscard
  split_ifs
  · exact le_refl _
  · rw [dist_self]; exact dist_nonneg

omit [MetricSpace Arch] in
/-- **Constraint preservation for constrained keep/discard**: if C(a) then C(δ(a)).
    The constraint is checked before accepting, so preserved non-trivially. -/
theorem constrainedKeepDiscard_constraint (E : Arch → ℝ) (propose : Arch → Arch)
    (C : Arch → Prop) (a : Arch) (ha : C a) :
    C (constrainedKeepDiscard E propose C a) := by
  unfold constrainedKeepDiscard
  split_ifs with h
  · exact h.2
  · exact ha

open Classical in
/-- **Constrained Autoresearch as SOS**: concrete construction with non-trivial
    constraint preservation. The constraint C is arbitrary (e.g., parameter budget,
    latency bound). -/
noncomputable def constrainedAutoresearchSOS
    (E : Arch → ℝ) (propose : Arch → Arch) (C : Arch → Prop)
    (hE_bdd : BddAbove (Set.range E))
    (D : ℝ) (hD : D > 0)
    (hPropose_bdd : ∀ a : Arch, dist (propose a) a ≤ D) : SOS where
  Pi := Arch
  E := E
  E_bddAbove := hE_bdd
  Delta := D
  Delta_pos := hD
  C := C
  delta := constrainedKeepDiscard E propose C
  monotone_improvement := constrainedKeepDiscard_monotone E propose C
  bounded_step := fun a =>
    (constrainedKeepDiscard_bounded E propose C a).trans (hPropose_bdd a)
  constraint_preservation := constrainedKeepDiscard_constraint E propose C

/-- Constrained autoresearch convergence: free theorem. -/
theorem constrained_autoresearch_convergence
    (E : Arch → ℝ) (propose : Arch → Arch) (C : Arch → Prop)
    (hE_bdd : BddAbove (Set.range E))
    (D : ℝ) (hD : D > 0)
    (hPropose_bdd : ∀ a : Arch, dist (propose a) a ≤ D)
    (pi0 : Arch) :
    ∃ L : ℝ, Filter.Tendsto
      ((constrainedAutoresearchSOS E propose C hE_bdd D hD hPropose_bdd).orbit pi0)
      Filter.atTop (nhds L) :=
  (constrainedAutoresearchSOS E propose C hE_bdd D hD hPropose_bdd).convergence pi0

end ConstrainedAutoresearch

/-! ## EM (Expectation-Maximization): Concrete Construction

The classical EM algorithm (Dempster, Laird, Rubin 1977) alternates E-steps
and M-steps to maximise a log-likelihood.  The EM inequality guarantees
ℓ(θ') ≥ ℓ(θ) after each M-step, providing Monotone Improvement directly.
The log-likelihood is bounded above (by 0 for normalised models, or by a
finite constant for bounded observation spaces).

The EM inequality is taken as a hypothesis parameter, not an axiom:
it is proven in standard EM theory and holds unconditionally. -/

section EM

/-- **EM as a concrete SOS**: The EM inequality provides monotone improvement
    directly.  No axioms needed---the EM inequality is a hypothesis parameter,
    proven in textbook EM theory (Dempster et al., 1977). -/
noncomputable def emSOS
    {Theta : Type*} [MetricSpace Theta]
    (loglik : Theta → ℝ) (emStep : Theta → Theta)
    (hLoglik_bdd : BddAbove (Set.range loglik))
    (hEM_ineq : ∀ θ, loglik (emStep θ) ≥ loglik θ)
    (D : ℝ) (hD : D > 0)
    (hStep_bdd : ∀ θ, dist (emStep θ) θ ≤ D) : SOS where
  Pi := Theta
  E := loglik
  E_bddAbove := hLoglik_bdd
  Delta := D
  Delta_pos := hD
  C := fun _ => True
  delta := emStep
  monotone_improvement := hEM_ineq
  bounded_step := hStep_bdd
  constraint_preservation := fun _ _ => trivial

/-- EM convergence: free theorem from the concrete construction. -/
theorem em_convergence
    {Theta : Type*} [MetricSpace Theta]
    (loglik : Theta → ℝ) (emStep : Theta → Theta)
    (hLoglik_bdd : BddAbove (Set.range loglik))
    (hEM_ineq : ∀ θ, loglik (emStep θ) ≥ loglik θ)
    (D : ℝ) (hD : D > 0)
    (hStep_bdd : ∀ θ, dist (emStep θ) θ ≤ D)
    (θ0 : Theta) :
    ∃ L : ℝ, Filter.Tendsto
      ((emSOS loglik emStep hLoglik_bdd hEM_ineq D hD hStep_bdd).orbit θ0)
      Filter.atTop (nhds L) :=
  (emSOS loglik emStep hLoglik_bdd hEM_ineq D hD hStep_bdd).convergence θ0

/-- **Constrained EM**: EM with non-trivial constraint via constraint lifting.
    One-line construction demonstrating SOS modularity. -/
noncomputable def constrainedEmSOS
    {Theta : Type*} [MetricSpace Theta]
    (loglik : Theta → ℝ) (emStep : Theta → Theta)
    (hLoglik_bdd : BddAbove (Set.range loglik))
    (hEM_ineq : ∀ θ, loglik (emStep θ) ≥ loglik θ)
    (D : ℝ) (hD : D > 0)
    (hStep_bdd : ∀ θ, dist (emStep θ) θ ≤ D)
    (C : Theta → Prop) : SOS :=
  (emSOS loglik emStep hLoglik_bdd hEM_ineq D hD hStep_bdd).constraintLift C

/-- Constrained EM convergence: free theorem from constraint lifting. -/
theorem constrained_em_convergence
    {Theta : Type*} [MetricSpace Theta]
    (loglik : Theta → ℝ) (emStep : Theta → Theta)
    (hLoglik_bdd : BddAbove (Set.range loglik))
    (hEM_ineq : ∀ θ, loglik (emStep θ) ≥ loglik θ)
    (D : ℝ) (hD : D > 0)
    (hStep_bdd : ∀ θ, dist (emStep θ) θ ≤ D)
    (C : Theta → Prop) (θ0 : Theta) :
    ∃ L : ℝ, Filter.Tendsto
      ((constrainedEmSOS loglik emStep hLoglik_bdd hEM_ineq D hD hStep_bdd C).orbit θ0)
      Filter.atTop (nhds L) :=
  (constrainedEmSOS loglik emStep hLoglik_bdd hEM_ineq D hD hStep_bdd C).convergence θ0

end EM

/-! ## Exact Policy Iteration: Concrete RL Instantiation

Exact policy iteration on finite MDPs. The policy improvement theorem
(Puterman, 2005) guarantees V(improve(π)) ≥ V(π) unconditionally, giving
a concrete RL instantiation with no axioms needed.

The MDP structure is parameterized; the key property (monotone improvement
via the policy improvement theorem) is provided as a hypothesis. -/

section ExactPolicyIteration

/-- **Exact Policy Iteration as SOS**: The policy improvement theorem guarantees
    monotone improvement unconditionally for finite MDPs, so no axioms are needed.
    Contrast with PPO, which requires an axiom because standard PPO achieves
    only approximate ascent. -/
noncomputable def exactPISOS
    {Policy : Type*} [MetricSpace Policy]
    (V : Policy → ℝ) (improve : Policy → Policy)
    (hV_bdd : BddAbove (Set.range V))
    (hPI_monotone : ∀ π, V (improve π) ≥ V π)
    (D : ℝ) (hD : D > 0)
    (hImprove_bdd : ∀ π, dist (improve π) π ≤ D) : SOS where
  Pi := Policy
  E := V
  E_bddAbove := hV_bdd
  Delta := D
  Delta_pos := hD
  C := fun _ => True
  delta := improve
  monotone_improvement := hPI_monotone
  bounded_step := hImprove_bdd
  constraint_preservation := fun _ _ => trivial

/-- Exact policy iteration convergence: free theorem. -/
theorem exact_pi_convergence
    {Policy : Type*} [MetricSpace Policy]
    (V : Policy → ℝ) (improve : Policy → Policy)
    (hV_bdd : BddAbove (Set.range V))
    (hPI_monotone : ∀ π, V (improve π) ≥ V π)
    (D : ℝ) (hD : D > 0)
    (hImprove_bdd : ∀ π, dist (improve π) π ≤ D)
    (π0 : Policy) :
    ∃ L : ℝ, Filter.Tendsto
      ((exactPISOS V improve hV_bdd hPI_monotone D hD hImprove_bdd).orbit π0)
      Filter.atTop (nhds L) :=
  (exactPISOS V improve hV_bdd hPI_monotone D hD hImprove_bdd).convergence π0

end ExactPolicyIteration

/-! ## Safe Policy Iteration: Constraint Lifting Applied

Demonstrates constraint lifting on a concrete system.  Safe PI accepts
the greedy improvement only if the new policy satisfies a safety
predicate.  This is a one-line composition of exactPISOS and constraintLift,
demonstrating the modularity of the SOS framework. -/

section SafePolicyIteration

/-- **Safe policy iteration**: exact PI with non-trivial constraint
    via constraint lifting.  Convergence is a free theorem. -/
noncomputable def safePISOS
    {Policy : Type*} [MetricSpace Policy]
    (V : Policy → ℝ) (improve : Policy → Policy)
    (hV_bdd : BddAbove (Set.range V))
    (hPI_monotone : ∀ π, V (improve π) ≥ V π)
    (D : ℝ) (hD : D > 0)
    (hImprove_bdd : ∀ π, dist (improve π) π ≤ D)
    (Safe : Policy → Prop) : SOS :=
  (exactPISOS V improve hV_bdd hPI_monotone D hD hImprove_bdd).constraintLift Safe

/-- Safe PI convergence: free theorem from constraint lifting. -/
theorem safe_pi_convergence
    {Policy : Type*} [MetricSpace Policy]
    (V : Policy → ℝ) (improve : Policy → Policy)
    (hV_bdd : BddAbove (Set.range V))
    (hPI_monotone : ∀ π, V (improve π) ≥ V π)
    (D : ℝ) (hD : D > 0)
    (hImprove_bdd : ∀ π, dist (improve π) π ≤ D)
    (Safe : Policy → Prop) (π0 : Policy) :
    ∃ L : ℝ, Filter.Tendsto
      ((safePISOS V improve hV_bdd hPI_monotone D hD hImprove_bdd Safe).orbit π0)
      Filter.atTop (nhds L) :=
  (safePISOS V improve hV_bdd hPI_monotone D hD hImprove_bdd Safe).convergence π0

end SafePolicyIteration

/-! ## ECEF: Concrete Construction

The Expert Cognitive Extraction Framework uses append-only refinement:
each extraction session can only ADD knowledge, never remove it.
If the evaluator is monotone in knowledge level, monotone improvement follows. -/

section ECEF

/-- **ECEF as a concrete SOS** (Phase B2): No axioms needed.
    Modeled with a monotone refinement operator on a metric space.
    Key assumption: refine(x) always "improves" x in the evaluator's view,
    i.e., E(refine(x)) ≥ E(x). This captures the append-only property. -/
noncomputable def ecefSOS
    {Encoding : Type*} [MetricSpace Encoding]
    (E : Encoding → ℝ) (refine : Encoding → Encoding)
    (hE_bdd : BddAbove (Set.range E))
    (hRefine_improves : ∀ x, E (refine x) ≥ E x)
    (D : ℝ) (hD : D > 0)
    (hRefine_bdd : ∀ x, dist (refine x) x ≤ D) : SOS where
  Pi := Encoding
  E := E
  E_bddAbove := hE_bdd
  Delta := D
  Delta_pos := hD
  C := fun _ => True
  delta := refine
  monotone_improvement := hRefine_improves
  bounded_step := hRefine_bdd
  constraint_preservation := fun _ _ => trivial

/-- ECEF convergence: free theorem from the concrete construction. -/
theorem ecef_convergence
    {Encoding : Type*} [MetricSpace Encoding]
    (E : Encoding → ℝ) (refine : Encoding → Encoding)
    (hE_bdd : BddAbove (Set.range E))
    (hRefine_improves : ∀ x, E (refine x) ≥ E x)
    (D : ℝ) (hD : D > 0)
    (hRefine_bdd : ∀ x, dist (refine x) x ≤ D)
    (x0 : Encoding) :
    ∃ L : ℝ, Filter.Tendsto
      ((ecefSOS E refine hE_bdd hRefine_improves D hD hRefine_bdd).orbit x0)
      Filter.atTop (nhds L) :=
  (ecefSOS E refine hE_bdd hRefine_improves D hD hRefine_bdd).convergence x0

/-- **Constrained ECEF**: ECEF with non-trivial constraint via constraint lifting.
    E.g., encoding must fit within a token budget or satisfy a structural predicate. -/
noncomputable def constrainedEcefSOS
    {Encoding : Type*} [MetricSpace Encoding]
    (E : Encoding → ℝ) (refine : Encoding → Encoding)
    (hE_bdd : BddAbove (Set.range E))
    (hRefine_improves : ∀ x, E (refine x) ≥ E x)
    (D : ℝ) (hD : D > 0)
    (hRefine_bdd : ∀ x, dist (refine x) x ≤ D)
    (C : Encoding → Prop) : SOS :=
  (ecefSOS E refine hE_bdd hRefine_improves D hD hRefine_bdd).constraintLift C

/-- Constrained ECEF convergence: free theorem from constraint lifting. -/
theorem constrained_ecef_convergence
    {Encoding : Type*} [MetricSpace Encoding]
    (E : Encoding → ℝ) (refine : Encoding → Encoding)
    (hE_bdd : BddAbove (Set.range E))
    (hRefine_improves : ∀ x, E (refine x) ≥ E x)
    (D : ℝ) (hD : D > 0)
    (hRefine_bdd : ∀ x, dist (refine x) x ≤ D)
    (C : Encoding → Prop) (x0 : Encoding) :
    ∃ L : ℝ, Filter.Tendsto
      ((constrainedEcefSOS E refine hE_bdd hRefine_improves D hD hRefine_bdd C).orbit x0)
      Filter.atTop (nhds L) :=
  (constrainedEcefSOS E refine hE_bdd hRefine_improves D hD hRefine_bdd C).convergence x0

end ECEF

/-! ## Inter-Instance Morphisms

The SOS hierarchy forms a directed chain: PPO → Autoresearch → ECEF.
PPO → Autoresearch: trust-region updates embed into keep/discard architecture search.
Autoresearch → ECEF: architecture search embeds into cognitive extraction refinement.
PPO → ECEF: derived by composition (not axiomatized).

PPO morphisms are axiomatized because PPO_is_SOS is abstract. The Autoresearch → ECEF
morphism is axiomatized because the embedding f : Arch → Encoding (mapping architectures
to knowledge encodings such that keep/discard corresponds to refinement) requires
domain-specific structure beyond what SOS alone can construct. -/

/-- PPO → Autoresearch morphism: trust-region policy updates embed into the
    keep/discard architecture search mechanism. Axiomatized because PPO_is_SOS
    is abstract — we cannot construct f : PPO_is_SOS.Pi → Arch without knowing
    PPO's concrete policy space. -/
axiom PPO_to_Autoresearch_morphism
    {Arch : Type*} [MetricSpace Arch]
    (E : Arch → ℝ) (propose : Arch → Arch)
    (hE_bdd : BddAbove (Set.range E))
    (D : ℝ) (hD : D > 0)
    (hPropose_bdd : ∀ a : Arch, dist (propose a) a ≤ D) :
    SOS.Morphism PPO_is_SOS (autoresearchSOS E propose hE_bdd D hD hPropose_bdd)

/-- Autoresearch → ECEF morphism: architecture search (keep/discard) embeds into
    cognitive extraction (append-only refinement). This is the key structural claim:
    that searching for better architectures IS a form of knowledge extraction,
    with an embedding f : Arch → Encoding such that the keep/discard process
    in architecture space corresponds to the refinement process in encoding space.
    Axiomatized because constructing this embedding requires domain-specific
    knowledge about how architectures encode expert cognition. -/
axiom Autoresearch_to_ECEF_morphism
    {Arch : Type*} [MetricSpace Arch]
    (E_A : Arch → ℝ) (propose : Arch → Arch)
    (hE_A_bdd : BddAbove (Set.range E_A))
    (D_A : ℝ) (hD_A : D_A > 0)
    (hPropose_bdd : ∀ a : Arch, dist (propose a) a ≤ D_A)
    {Encoding : Type*} [MetricSpace Encoding]
    (E_E : Encoding → ℝ) (refine : Encoding → Encoding)
    (hE_E_bdd : BddAbove (Set.range E_E))
    (hRefine_improves : ∀ x, E_E (refine x) ≥ E_E x)
    (D_E : ℝ) (hD_E : D_E > 0)
    (hRefine_bdd : ∀ x, dist (refine x) x ≤ D_E) :
    SOS.Morphism
      (autoresearchSOS E_A propose hE_A_bdd D_A hD_A hPropose_bdd)
      (ecefSOS E_E refine hE_E_bdd hRefine_improves D_E hD_E hRefine_bdd)

universe u in
/-- PPO → ECEF morphism: **derived by composition**, not axiomatized.
    The directed chain PPO → Autoresearch → ECEF composes to give a direct
    embedding of PPO into ECEF. Universe annotation ensures Arch and Encoding
    live in the same universe so SOS.Morphism.comp can unify its three
    SOS arguments (S1 = PPO, S2 = autoresearchSOS, S3 = ecefSOS). -/
noncomputable def PPO_to_ECEF_morphism
    {Arch : Type u} [MetricSpace Arch]
    (E_A : Arch → ℝ) (propose : Arch → Arch)
    (hE_A_bdd : BddAbove (Set.range E_A))
    (D_A : ℝ) (hD_A : D_A > 0)
    (hPropose_bdd : ∀ a : Arch, dist (propose a) a ≤ D_A)
    {Encoding : Type u} [MetricSpace Encoding]
    (E_E : Encoding → ℝ) (refine : Encoding → Encoding)
    (hE_E_bdd : BddAbove (Set.range E_E))
    (hRefine_improves : ∀ x, E_E (refine x) ≥ E_E x)
    (D_E : ℝ) (hD_E : D_E > 0)
    (hRefine_bdd : ∀ x, dist (refine x) x ≤ D_E) :
    SOS.Morphism PPO_is_SOS (ecefSOS E_E refine hE_E_bdd hRefine_improves D_E hD_E hRefine_bdd) :=
  (Autoresearch_to_ECEF_morphism E_A propose hE_A_bdd D_A hD_A hPropose_bdd
    E_E refine hE_E_bdd hRefine_improves D_E hD_E hRefine_bdd).comp
  (PPO_to_Autoresearch_morphism E_A propose hE_A_bdd D_A hD_A hPropose_bdd)

/-! ### Lax Morphism Chain: PPO ⇝ Autoresearch ⇝ ECEF

The lax morphism framework enables a weaker formulation of the
Autoresearch → ECEF connection.  Instead of exact update commutativity
  f(keepDiscard(a)) = refine(f(a))
we require only the evaluator-level inequality
  E_E(f(keepDiscard(a))) ≥ E_E(refine(f(a)))
meaning: the extraction quality of the selected architecture is at
least as good as refining the current extraction.

The PPO → Autoresearch leg remains a strict axiom (converted to lax
via toLaxMorphism).  The full chain PPO ⇝ ECEF is derived by lax
composition — not axiomatized. -/

/-- **Lax Autoresearch → ECEF morphism**: parameterized construction
    with a strictly weaker hypothesis than the strict axiom.
    The map f : Arch → Encoding and evaluator bridge g are parameters;
    the lax update condition is a hypothesis, not a global axiom.
    Compare with `Autoresearch_to_ECEF_morphism` (strict, axiomatized). -/
noncomputable def Autoresearch_to_ECEF_lax_morphism
    {Arch : Type*} [MetricSpace Arch]
    (E_A : Arch → ℝ) (propose : Arch → Arch)
    (hE_A_bdd : BddAbove (Set.range E_A))
    (D_A : ℝ) (hD_A : D_A > 0)
    (hPropose_bdd : ∀ a : Arch, dist (propose a) a ≤ D_A)
    {Encoding : Type*} [MetricSpace Encoding]
    (E_E : Encoding → ℝ) (refine : Encoding → Encoding)
    (hE_E_bdd : BddAbove (Set.range E_E))
    (hRefine_improves : ∀ x, E_E (refine x) ≥ E_E x)
    (D_E : ℝ) (hD_E : D_E > 0)
    (hRefine_bdd : ∀ x, dist (refine x) x ≤ D_E)
    -- Domain-specific parameters (strictly weaker than strict axiom):
    (f : Arch → Encoding)
    (g : ℝ → ℝ)
    (hg_mono : Monotone g)
    (heval : ∀ a : Arch, g (E_A a) = E_E (f a))
    (hlax : ∀ a : Arch,
      E_E (f (keepDiscard E_A propose a)) ≥ E_E (refine (f a))) :
    SOS.LaxMorphism
      (autoresearchSOS E_A propose hE_A_bdd D_A hD_A hPropose_bdd)
      (ecefSOS E_E refine hE_E_bdd hRefine_improves D_E hD_E hRefine_bdd) where
  f := f
  g := g
  g_monotone := hg_mono
  evaluator_compat := heval
  lax_update := hlax
  constraint_compat := fun _ _ => trivial

universe u' in
/-- PPO → ECEF via lax composition: the strict PPO → Autoresearch morphism
    is embedded as lax, then composed with the lax Autoresearch → ECEF
    morphism.  The result is a lax morphism derived by composition — not
    axiomatized.  Compare with `PPO_to_ECEF_morphism` (strict chain). -/
noncomputable def PPO_to_ECEF_lax_morphism
    {Arch : Type u'} [MetricSpace Arch]
    (E_A : Arch → ℝ) (propose : Arch → Arch)
    (hE_A_bdd : BddAbove (Set.range E_A))
    (D_A : ℝ) (hD_A : D_A > 0)
    (hPropose_bdd : ∀ a : Arch, dist (propose a) a ≤ D_A)
    {Encoding : Type u'} [MetricSpace Encoding]
    (E_E : Encoding → ℝ) (refine : Encoding → Encoding)
    (hE_E_bdd : BddAbove (Set.range E_E))
    (hRefine_improves : ∀ x, E_E (refine x) ≥ E_E x)
    (D_E : ℝ) (hD_E : D_E > 0)
    (hRefine_bdd : ∀ x, dist (refine x) x ≤ D_E)
    (f : Arch → Encoding)
    (g : ℝ → ℝ)
    (hg_mono : Monotone g)
    (heval : ∀ a : Arch, g (E_A a) = E_E (f a))
    (hlax : ∀ a : Arch,
      E_E (f (keepDiscard E_A propose a)) ≥ E_E (refine (f a))) :
    SOS.LaxMorphism PPO_is_SOS
      (ecefSOS E_E refine hE_E_bdd hRefine_improves D_E hD_E hRefine_bdd) :=
  (Autoresearch_to_ECEF_lax_morphism E_A propose hE_A_bdd D_A hD_A hPropose_bdd
    E_E refine hE_E_bdd hRefine_improves D_E hD_E hRefine_bdd
    f g hg_mono heval hlax).comp
  (PPO_to_Autoresearch_morphism E_A propose hE_A_bdd D_A hD_A hPropose_bdd).toLaxMorphism

/-! # Phase 5: Lipschitz Bounds (Spectral Normalization) -/

/-- A spectrally normalized function: a real-valued function with a proven
    Lipschitz bound. If W̄_SN(W) = W/σ(W) is applied to every layer of an
    L-layer network, the composite function has bounded sensitivity. -/
structure SpectrallyNormalized where
  /-- The function (simplified to ℝ → ℝ; full encoding uses normed spaces) -/
  f : ℝ → ℝ
  /-- The Lipschitz constant -/
  L : ℝ
  /-- L is positive -/
  L_pos : L > 0
  /-- The Lipschitz bound: ‖f(x) - f(y)‖ ≤ L · ‖x - y‖ -/
  lipschitz : LipschitzWith (Real.toNNReal L) f

/-- **Triple Safety Bound**: If three independent safety mechanisms each bound
    deviation by L₁, L₂, L₃, the composite bounds deviation by L₁ · L₂ · L₃.
    Spectral Normalization × Trust Region × Constraint Projection. -/
theorem triple_safety_bound
    (f1 f2 f3 : ℝ → ℝ)
    (L1 L2 L3 : NNReal)
    (h1 : LipschitzWith L1 f1)
    (h2 : LipschitzWith L2 f2)
    (h3 : LipschitzWith L3 f3) :
    LipschitzWith (L1 * L2 * L3) (f1 ∘ f2 ∘ f3) := by
  rw [mul_assoc]
  exact h1.comp (h2.comp h3)

/-- **Lipschitz-SOS connection**: If the update operator δ is a contraction
    (Lipschitz with K < 1), then the orbit in policy space is Cauchy.
    Bridges Phase 5's Lipschitz machinery with Phase 1's SOS structure. -/
theorem SOS.lipschitz_orbit_cauchy (S : SOS) (pi0 : S.Pi)
    (K : NNReal) (hK : (K : ℝ) < 1)
    (hLip : LipschitzWith K S.delta) :
    CauchySeq (fun n => S.delta^[n] pi0) := by
  apply cauchySeq_of_le_geometric (↑K) (dist pi0 (S.delta pi0)) hK
  intro n
  exact hLip.dist_iterate_succ_le_geometric pi0 n

/-! # Phase 6: Policy Space Convergence

The core SOS theorem gives convergence of the evaluator sequence E(δ^[n](π₀)) in ℝ.
With additional structure — completeness of Π and contractivity of δ — we get
convergence of the policy orbit δ^[n](π₀) itself in the metric space Π. -/

/-- **Policy orbit convergence** (Phase A2): In a complete metric space, if δ is
    a contraction (Lipschitz with K < 1), the policy orbit converges to some π*.
    This goes beyond evaluator convergence to show the policies themselves converge. -/
theorem SOS.policy_orbit_converges (S : SOS) [CompleteSpace S.Pi] (pi0 : S.Pi)
    (K : NNReal) (hK : (K : ℝ) < 1)
    (hLip : LipschitzWith K S.delta) :
    ∃ pi_star : S.Pi,
      Filter.Tendsto (fun n => S.delta^[n] pi0) Filter.atTop (nhds pi_star) :=
  cauchySeq_tendsto_of_complete (S.lipschitz_orbit_cauchy pi0 K hK hLip)

/-- **Fixed-point theorem**: If δ is continuous and the policy orbit δ^[n](π₀)
    converges to π*, then π* is a fixed point of δ: δ(π*) = π*.
    This is purely topological — no contraction, completeness, or Lipschitz needed.
    Proof: δ^[n+1](π₀) → π* (shifted tail of convergent sequence) and
    δ^[n+1](π₀) = δ(δ^[n](π₀)) → δ(π*) (continuity). By limit uniqueness, δ(π*) = π*. -/
theorem SOS.limit_is_fixed_point (S : SOS) (pi0 : S.Pi)
    {pi_star : S.Pi}
    (hpi : Filter.Tendsto (fun n => S.delta^[n] pi0) Filter.atTop (nhds pi_star))
    (hdelta_cont : Continuous S.delta) :
    S.delta pi_star = pi_star := by
  -- δ^[n+1](π₀) → δ(π*) by continuity of δ
  have hsucc : Filter.Tendsto (fun n => S.delta^[n + 1] pi0)
      Filter.atTop (nhds (S.delta pi_star)) := by
    have heq : ∀ n, S.delta^[n + 1] pi0 = S.delta (S.delta^[n] pi0) := fun n =>
      congr_fun (Function.iterate_succ' S.delta n) pi0
    simp_rw [heq]
    exact (hdelta_cont.tendsto pi_star).comp hpi
  -- δ^[n+1](π₀) → π* (shifted tail of convergent sequence)
  have hshift : Filter.Tendsto (fun n => S.delta^[n + 1] pi0)
      Filter.atTop (nhds pi_star) :=
    hpi.comp (Filter.tendsto_atTop_atTop_of_monotone
      (fun _ _ h => Nat.add_le_add_right h 1) fun b => ⟨b, Nat.le_add_right b 1⟩)
  -- Both target the same sequence, so δ(π*) = π*
  exact tendsto_nhds_unique hsucc hshift

/-- **Evaluator stationarity**: E is stationary at the fixed point.
    Trivial corollary of `limit_is_fixed_point`: δ(π*) = π* implies E(δ(π*)) = E(π*). -/
theorem SOS.evaluator_stationary_at_limit (S : SOS) (pi0 : S.Pi)
    {pi_star : S.Pi}
    (hpi : Filter.Tendsto (fun n => S.delta^[n] pi0) Filter.atTop (nhds pi_star))
    (hdelta_cont : Continuous S.delta) :
    S.E (S.delta pi_star) = S.E pi_star :=
  congr_arg S.E (S.limit_is_fixed_point pi0 hpi hdelta_cont)
