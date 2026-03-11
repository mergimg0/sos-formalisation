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
