/-
  PowerLaw.lean — Power-Law Convergence Rates for Sacred Object Systems

  Extends the SOS framework with sublinear convergence rates under
  power-law Łojasiewicz conditions.  The geometric rate theorem in
  Basic.lean handles α = 1 (linear Łojasiewicz); this file handles
  α = 2 (quadratic Łojasiewicz), giving O(1/n) convergence rates.

  Key results:
  - power_law_rate_alpha2: O(1/n) rate under quadratic Łojasiewicz
  - local_power_law_rate_alpha2: basin-restricted version
  - lipschitz_rate_transfer_alpha2: Lipschitz morphisms preserve O(1/n) rate
  - holder_rate_transfer_alpha2: Hölder morphisms give O(n^{-β}) rate (headline result)

  Phase 1a proofs use pure algebra; Phase 1b Hölder transfer uses rpow.
-/

import SosFormalization.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! ## Phase 1a: Power-Law Rate for α = 2

The quadratic Łojasiewicz condition E(δ(π)) - E(π) ≥ c · (M - E(π))²
arises naturally from gradient descent on L-smooth convex functions.
The gap e_n = M - orbit(n) satisfies e_{n+1} ≤ e_n - c·e_n², giving
the O(1/n) rate e_n ≤ e_0/(1 + c·e_0·n).

The proof uses the multiplication form: (M - orbit(n))·(1 + c·e₀·n) ≤ e₀,
avoiding all division in the induction.  The key algebraic step factors as
(a + b)(1 - b) ≤ (1 + b)(1 - b) = 1 - b² ≤ 1, where a ≤ 1 is the IH. -/

/-- The gap M - orbit(n) is non-negative (from monotone improvement + bound). -/
lemma SOS.gap_nonneg (S : SOS) (pi0 : S.Pi)
    {M : ℝ} (hM : ∀ (π : S.Pi), S.E π ≤ M) (n : ℕ) :
    0 ≤ M - S.orbit pi0 n := by
  simp only [SOS.orbit]
  linarith [hM (S.delta^[n] pi0)]

/-- The gap is non-increasing: orbit is monotone so M - orbit(n) ≤ M - orbit(0). -/
lemma SOS.gap_le_initial (S : SOS) (pi0 : S.Pi)
    {M : ℝ} (_hM : ∀ π : S.Pi, S.E π ≤ M) (n : ℕ) :
    M - S.orbit pi0 n ≤ M - S.E pi0 := by
  have := S.orbit_monotone pi0
  simp only [SOS.orbit] at *
  have h0 : S.E pi0 ≤ S.E (S.delta^[n] pi0) := by
    have : S.E (S.delta^[0] pi0) ≤ S.E (S.delta^[n] pi0) := this (Nat.zero_le n)
    simpa using this
  linarith

/-- The small-constant condition c·e₀^p ≤ 1 is derivable from the
    Łojasiewicz condition and the upper bound M: the per-step improvement
    c·e₀^{p+1} cannot exceed the gap e₀, so c·e₀^p ≤ 1. -/
lemma SOS.loj_implies_small (S : SOS) (pi0 : S.Pi) (p : ℕ) (hp : 1 ≤ p)
    {M : ℝ} (hM : ∀ π : S.Pi, S.E π ≤ M)
    {c : ℝ} (_hc_pos : 0 < c)
    (hLoj : ∀ π : S.Pi, S.E (S.delta π) - S.E π ≥ c * (M - S.E π) ^ (p + 1))
    : c * (M - S.E pi0) ^ p ≤ 1 := by
  by_contra h
  push_neg at h
  set e0 := M - S.E pi0
  have he0_nn : 0 ≤ e0 := by linarith [hM pi0]
  have he0_pos : 0 < e0 := by
    rcases eq_or_lt_of_le he0_nn with he0_zero | hpos
    · exfalso; rw [← he0_zero] at h; simp [zero_pow (by omega : p ≠ 0)] at h; linarith
    · exact hpos
  have h_bound : e0 ≥ c * e0 ^ (p + 1) := by linarith [hLoj pi0, hM (S.delta pi0)]
  have h_contra : c * e0 ^ (p + 1) > e0 := by
    calc c * e0 ^ (p + 1) = c * e0 ^ p * e0 := by rw [pow_succ]; ring
      _ > 1 * e0 := mul_lt_mul_of_pos_right h he0_pos
      _ = e0 := one_mul e0
  linarith

/-- **Power-law convergence rate for α = 2** (multiplication form):
    Under a quadratic Łojasiewicz condition E(δ(π)) - E(π) ≥ c·(M - E(π))²,
    the gap satisfies (M - orbit(n))·(1 + c·e₀·n) ≤ e₀.
    This is the core inductive lemma; the division form follows. -/
theorem SOS.power_law_mul_alpha2 (S : SOS) (pi0 : S.Pi)
    {M : ℝ} (hM : ∀ π : S.Pi, S.E π ≤ M)
    {c : ℝ} (hc_pos : 0 < c)
    (hLoj : ∀ π : S.Pi, S.E (S.delta π) - S.E π ≥ c * (M - S.E π) ^ 2)
    (n : ℕ) :
    (M - S.orbit pi0 n) * (1 + c * (M - S.E pi0) * ↑n) ≤ M - S.E pi0 := by
  set e0 := M - S.E pi0 with he0_def
  have he0_nn : 0 ≤ e0 := by linarith [hM pi0]
  have hc_small : c * e0 ≤ 1 := by
    have h := S.loj_implies_small pi0 1 le_rfl hM hc_pos hLoj; rwa [pow_one] at h
  induction n with
  | zero =>
    simp only [SOS.orbit, Function.iterate_zero, id_eq, Nat.cast_zero, mul_zero, add_zero,
               mul_one]
    exact le_refl _
  | succ n ih =>
    set en := M - S.orbit pi0 n
    -- Key facts about en
    have hen_nn : 0 ≤ en := S.gap_nonneg pi0 hM n
    have hen_le : en ≤ e0 := S.gap_le_initial pi0 hM n
    have hcen_le : c * en ≤ 1 :=
      le_trans (mul_le_mul_of_nonneg_left hen_le (le_of_lt hc_pos)) hc_small
    -- The Łojasiewicz step: e_{n+1} ≤ en - c·en²
    have hstep : M - S.orbit pi0 (n + 1) ≤ en - c * en ^ 2 := by
      change M - S.orbit pi0 (n + 1) ≤ (M - S.orbit pi0 n) - c * (M - S.orbit pi0 n) ^ 2
      simp only [SOS.orbit, Function.iterate_succ', Function.comp_apply]
      linarith [hLoj (S.delta^[n] pi0)]
    -- Factor: en - c·en² = en·(1 - c·en)
    have hen1_le : M - S.orbit pi0 (n + 1) ≤ en * (1 - c * en) := by linarith [hstep]
    have h1_sub_nn : 0 ≤ 1 - c * en := by linarith
    -- Normalize ↑(n+1) to ↑n + 1 in the goal
    simp only [Nat.cast_succ]
    have hden_nn : 0 ≤ 1 + c * e0 * (↑n + 1) := by positivity
    calc (M - S.orbit pi0 (n + 1)) * (1 + c * e0 * (↑n + 1))
        ≤ en * (1 - c * en) * (1 + c * e0 * (↑n + 1)) :=
          mul_le_mul_of_nonneg_right hen1_le hden_nn
      _ = en * (1 + c * e0 * ↑n) * (1 - c * en)
          + c * e0 * en * (1 - c * en) := by ring
      _ ≤ e0 * (1 - c * en) + c * e0 * en * (1 - c * en) := by
          linarith [mul_le_mul_of_nonneg_right ih h1_sub_nn]
      _ = e0 * (1 + c * en) * (1 - c * en) := by ring
      _ = e0 * (1 - (c * en) ^ 2) := by ring
      _ ≤ e0 := by nlinarith [sq_nonneg (c * en)]

/-- **Power-law convergence rate for α = 2** (division form):
    Under E(δ(π)) - E(π) ≥ c·(M - E(π))², the gap decays as O(1/n):
    M - orbit(n) ≤ e₀ / (1 + c·e₀·n). -/
theorem SOS.power_law_rate_alpha2 (S : SOS) (pi0 : S.Pi)
    {M : ℝ} (hM : ∀ π : S.Pi, S.E π ≤ M)
    {c : ℝ} (hc_pos : 0 < c)
    (hLoj : ∀ π : S.Pi, S.E (S.delta π) - S.E π ≥ c * (M - S.E π) ^ 2)
    (n : ℕ) :
    M - S.orbit pi0 n ≤ (M - S.E pi0) / (1 + c * (M - S.E pi0) * ↑n) := by
  have he0_nn : 0 ≤ M - S.E pi0 := by linarith [hM pi0]
  have hden_pos : 0 < 1 + c * (M - S.E pi0) * ↑n := by positivity
  rw [le_div_iff₀ hden_pos]
  exact S.power_law_mul_alpha2 pi0 hM hc_pos hLoj n

/-! ## Local Power-Law Rate for α = 2

Basin-restricted version: the Łojasiewicz condition holds only on a
δ-invariant subset B with local upper bound M_B.  Identical proof
structure to the global case; δ-invariance keeps iterates in B. -/

/-- Gap non-negativity on a basin. -/
lemma SOS.gap_nonneg_basin (S : SOS) (pi0 : S.Pi)
    {B : Set S.Pi} (hB : S.IsBasin B) (h0 : pi0 ∈ B)
    {M : ℝ} (hM : ∀ π ∈ B, S.E π ≤ M) (n : ℕ) :
    0 ≤ M - S.orbit pi0 n := by
  simp only [SOS.orbit]
  linarith [hM _ (S.iterate_mem_basin hB h0 n)]

/-- Gap ≤ initial gap on a basin. -/
lemma SOS.gap_le_initial_basin (S : SOS) (pi0 : S.Pi)
    {B : Set S.Pi} (_hB : S.IsBasin B) (_h0 : pi0 ∈ B)
    {M : ℝ} (_hM : ∀ π ∈ B, S.E π ≤ M) (n : ℕ) :
    M - S.orbit pi0 n ≤ M - S.E pi0 := by
  simp only [SOS.orbit]
  have h0n : S.E pi0 ≤ S.E (S.delta^[n] pi0) := by
    have := S.orbit_monotone pi0
    have : S.orbit pi0 0 ≤ S.orbit pi0 n := this (Nat.zero_le n)
    simpa [SOS.orbit] using this
  linarith

/-- Basin-restricted version of `loj_implies_small`. -/
lemma SOS.loj_implies_small_basin (S : SOS) (pi0 : S.Pi) (p : ℕ) (hp : 1 ≤ p)
    {B : Set S.Pi} (hB : S.IsBasin B) (h0 : pi0 ∈ B)
    {M : ℝ} (hM : ∀ π ∈ B, S.E π ≤ M)
    {c : ℝ} (_hc_pos : 0 < c)
    (hLoj : ∀ π ∈ B, S.E (S.delta π) - S.E π ≥ c * (M - S.E π) ^ (p + 1))
    : c * (M - S.E pi0) ^ p ≤ 1 := by
  by_contra h
  push_neg at h
  set e0 := M - S.E pi0
  have he0_nn : 0 ≤ e0 := by linarith [hM _ h0]
  have he0_pos : 0 < e0 := by
    rcases eq_or_lt_of_le he0_nn with he0_zero | hpos
    · exfalso; rw [← he0_zero] at h; simp [zero_pow (by omega : p ≠ 0)] at h; linarith
    · exact hpos
  have hdelta_mem : S.delta pi0 ∈ B := by
    have := S.iterate_mem_basin hB h0 1; rwa [Function.iterate_one] at this
  have h_bound : e0 ≥ c * e0 ^ (p + 1) := by linarith [hLoj _ h0, hM _ hdelta_mem]
  have h_contra : c * e0 ^ (p + 1) > e0 := by
    calc c * e0 ^ (p + 1) = c * e0 ^ p * e0 := by rw [pow_succ]; ring
      _ > 1 * e0 := mul_lt_mul_of_pos_right h he0_pos
      _ = e0 := one_mul e0
  linarith

/-- **Local power-law rate for α = 2** (multiplication form, basin-restricted). -/
theorem SOS.local_power_law_mul_alpha2 (S : SOS) (pi0 : S.Pi)
    {B : Set S.Pi} (hB : S.IsBasin B) (h0 : pi0 ∈ B)
    {M : ℝ} (hM : ∀ π ∈ B, S.E π ≤ M)
    {c : ℝ} (hc_pos : 0 < c)
    (hLoj : ∀ π ∈ B, S.E (S.delta π) - S.E π ≥ c * (M - S.E π) ^ 2)
    (n : ℕ) :
    (M - S.orbit pi0 n) * (1 + c * (M - S.E pi0) * ↑n) ≤ M - S.E pi0 := by
  set e0 := M - S.E pi0 with he0_def
  have he0_nn : 0 ≤ e0 := by linarith [hM _ h0]
  have hc_small : c * e0 ≤ 1 := by
    have h := S.loj_implies_small_basin pi0 1 le_rfl hB h0 hM hc_pos hLoj
    rwa [pow_one] at h
  induction n with
  | zero =>
    simp only [SOS.orbit, Function.iterate_zero, id_eq, Nat.cast_zero, mul_zero, add_zero,
               mul_one]
    exact le_refl _
  | succ n ih =>
    set en := M - S.orbit pi0 n
    have hmem : S.delta^[n] pi0 ∈ B := S.iterate_mem_basin hB h0 n
    have hen_nn : 0 ≤ en := S.gap_nonneg_basin pi0 hB h0 hM n
    have hen_le : en ≤ e0 := S.gap_le_initial_basin pi0 hB h0 hM n
    have hcen_le : c * en ≤ 1 :=
      le_trans (mul_le_mul_of_nonneg_left hen_le (le_of_lt hc_pos)) hc_small
    have hstep : M - S.orbit pi0 (n + 1) ≤ en - c * en ^ 2 := by
      change M - S.orbit pi0 (n + 1) ≤ (M - S.orbit pi0 n) - c * (M - S.orbit pi0 n) ^ 2
      simp only [SOS.orbit, Function.iterate_succ', Function.comp_apply]
      linarith [hLoj _ hmem]
    have hen1_le : M - S.orbit pi0 (n + 1) ≤ en * (1 - c * en) := by linarith [hstep]
    have h1_sub_nn : 0 ≤ 1 - c * en := by linarith
    -- Normalize ↑(n+1) to ↑n + 1 in the goal
    simp only [Nat.cast_succ]
    have hden_nn : 0 ≤ 1 + c * e0 * (↑n + 1) := by positivity
    calc (M - S.orbit pi0 (n + 1)) * (1 + c * e0 * (↑n + 1))
        ≤ en * (1 - c * en) * (1 + c * e0 * (↑n + 1)) :=
          mul_le_mul_of_nonneg_right hen1_le hden_nn
      _ = en * (1 + c * e0 * ↑n) * (1 - c * en)
          + c * e0 * en * (1 - c * en) := by ring
      _ ≤ e0 * (1 - c * en) + c * e0 * en * (1 - c * en) := by
          linarith [mul_le_mul_of_nonneg_right ih h1_sub_nn]
      _ = e0 * (1 + c * en) * (1 - c * en) := by ring
      _ = e0 * (1 - (c * en) ^ 2) := by ring
      _ ≤ e0 := by nlinarith [sq_nonneg (c * en)]

/-- **Local power-law rate for α = 2** (division form, basin-restricted). -/
theorem SOS.local_power_law_rate_alpha2 (S : SOS) (pi0 : S.Pi)
    {B : Set S.Pi} (hB : S.IsBasin B) (h0 : pi0 ∈ B)
    {M : ℝ} (hM : ∀ π ∈ B, S.E π ≤ M)
    {c : ℝ} (hc_pos : 0 < c)
    (hLoj : ∀ π ∈ B, S.E (S.delta π) - S.E π ≥ c * (M - S.E π) ^ 2)
    (n : ℕ) :
    M - S.orbit pi0 n ≤ (M - S.E pi0) / (1 + c * (M - S.E pi0) * ↑n) := by
  have he0_nn : 0 ≤ M - S.E pi0 := by linarith [hM _ h0]
  have hden_pos : 0 < 1 + c * (M - S.E pi0) * ↑n := by positivity
  rw [le_div_iff₀ hden_pos]
  exact S.local_power_law_mul_alpha2 pi0 hB h0 hM hc_pos hLoj n

/-- The global α = 2 rate is the special case B = Set.univ. -/
theorem SOS.power_law_rate_alpha2_of_local (S : SOS) (pi0 : S.Pi)
    {M : ℝ} (hM : ∀ π : S.Pi, S.E π ≤ M)
    {c : ℝ} (hc_pos : 0 < c)
    (hLoj : ∀ π : S.Pi, S.E (S.delta π) - S.E π ≥ c * (M - S.E π) ^ 2)
    (n : ℕ) :
    M - S.orbit pi0 n ≤ (M - S.E pi0) / (1 + c * (M - S.E pi0) * ↑n) :=
  S.local_power_law_rate_alpha2 pi0
    (B := Set.univ) (fun _ _ => Set.mem_univ _) (Set.mem_univ _)
    (fun π _ => hM π) hc_pos (fun π _ => hLoj π) n

/-! ## Lipschitz Rate Transfer for α = 2

If φ : S₁ → S₂ is a morphism with g being K-Lipschitz, and S₁ has
quadratic Łojasiewicz, the image orbit inherits the O(1/n) rate
scaled by K.  Follows the same pattern as `rate_transfer` in Basic.lean. -/

/-- **Lipschitz rate transfer for α = 2**: the image orbit decays as
    K · e₀ / (1 + c·e₀·n). -/
theorem SOS.Morphism.lipschitz_rate_transfer_alpha2 {S1 S2 : SOS}
    (phi : SOS.Morphism S1 S2) (pi0 : S1.Pi)
    {M : ℝ} (hM : ∀ π : S1.Pi, S1.E π ≤ M)
    {c : ℝ} (hc_pos : 0 < c)
    (hLoj : ∀ π : S1.Pi, S1.E (S1.delta π) - S1.E π ≥ c * (M - S1.E π) ^ 2)
    {K : ℝ} (hK : 0 ≤ K)
    (hg_lip : ∀ x y : ℝ, x ≤ y → phi.g y - phi.g x ≤ K * (y - x))
    (n : ℕ) :
    phi.g M - S2.orbit (phi.f pi0) n ≤
    K * ((M - S1.E pi0) / (1 + c * (M - S1.E pi0) * ↑n)) := by
  rw [phi.orbit_eq pi0 n]
  simp only [SOS.orbit]
  have hlip := hg_lip (S1.E (S1.delta^[n] pi0)) M (hM (S1.delta^[n] pi0))
  have hrate := S1.power_law_rate_alpha2 pi0 hM hc_pos hLoj n
  simp only [SOS.orbit] at hrate
  calc phi.g M - phi.g (S1.E (S1.delta^[n] pi0))
      ≤ K * (M - S1.E (S1.delta^[n] pi0)) := hlip
    _ ≤ K * ((M - S1.E pi0) / (1 + c * (M - S1.E pi0) * ↑n)) :=
        mul_le_mul_of_nonneg_left hrate hK

/-- **Local Lipschitz rate transfer for α = 2**: basin-restricted version. -/
theorem SOS.Morphism.local_lipschitz_rate_transfer_alpha2 {S1 S2 : SOS}
    (phi : SOS.Morphism S1 S2) (pi0 : S1.Pi)
    {B : Set S1.Pi} (hB : S1.IsBasin B) (h0 : pi0 ∈ B)
    {M : ℝ} (hM : ∀ π ∈ B, S1.E π ≤ M)
    {c : ℝ} (hc_pos : 0 < c)
    (hLoj : ∀ π ∈ B, S1.E (S1.delta π) - S1.E π ≥ c * (M - S1.E π) ^ 2)
    {K : ℝ} (hK : 0 ≤ K)
    (hg_lip : ∀ x y : ℝ, x ≤ y → phi.g y - phi.g x ≤ K * (y - x))
    (n : ℕ) :
    phi.g M - S2.orbit (phi.f pi0) n ≤
    K * ((M - S1.E pi0) / (1 + c * (M - S1.E pi0) * ↑n)) := by
  rw [phi.orbit_eq pi0 n]
  simp only [SOS.orbit]
  have hlip := hg_lip (S1.E (S1.delta^[n] pi0)) M
    (hM _ (S1.iterate_mem_basin hB h0 n))
  have hrate := S1.local_power_law_rate_alpha2 pi0 hB h0 hM hc_pos hLoj n
  simp only [SOS.orbit] at hrate
  calc phi.g M - phi.g (S1.E (S1.delta^[n] pi0))
      ≤ K * (M - S1.E (S1.delta^[n] pi0)) := hlip
    _ ≤ K * ((M - S1.E pi0) / (1 + c * (M - S1.E pi0) * ↑n)) :=
        mul_le_mul_of_nonneg_left hrate hK

/-! ## Hölder Rate Transfer for α = 2

If φ : S₁ → S₂ is a morphism with g being (K, β)-Hölder continuous
(g(y) - g(x) ≤ K · (y - x)^β for x ≤ y), and S₁ has quadratic
Łojasiewicz, the image orbit in S₂ decays as O(n^{-β}).

This is the headline novelty of the sequel paper: Hölder morphisms
distort convergence rates by the Hölder exponent β.  The Lipschitz case
(β = 1) recovers `lipschitz_rate_transfer_alpha2`.  When β < 1, the
rate degrades; when β > 1, it improves. -/

/-- **Hölder rate transfer for α = 2**: if φ.g is (K, β)-Hölder continuous
    and S₁ has quadratic Łojasiewicz, the image orbit decays as
    K · (e₀/(1 + c·e₀·n))^β = O(n^{-β}).  This is the quantitative
    Hölder distortion theorem. -/
theorem SOS.Morphism.holder_rate_transfer_alpha2 {S1 S2 : SOS}
    (phi : SOS.Morphism S1 S2) (pi0 : S1.Pi)
    {M : ℝ} (hM : ∀ π : S1.Pi, S1.E π ≤ M)
    {c : ℝ} (hc_pos : 0 < c)
    (hLoj : ∀ π : S1.Pi, S1.E (S1.delta π) - S1.E π ≥ c * (M - S1.E π) ^ 2)
    {K : ℝ} (hK : 0 ≤ K) {β : ℝ} (hβ : 0 < β)
    (hg_holder : ∀ x y : ℝ, x ≤ y → phi.g y - phi.g x ≤ K * (y - x) ^ β)
    (n : ℕ) :
    phi.g M - S2.orbit (phi.f pi0) n ≤
    K * ((M - S1.E pi0) / (1 + c * (M - S1.E pi0) * ↑n)) ^ β := by
  rw [phi.orbit_eq pi0 n]
  simp only [SOS.orbit]
  have hgap_nn : 0 ≤ M - S1.E (S1.delta^[n] pi0) := by linarith [hM (S1.delta^[n] pi0)]
  have hlip := hg_holder (S1.E (S1.delta^[n] pi0)) M (hM (S1.delta^[n] pi0))
  have hrate := S1.power_law_rate_alpha2 pi0 hM hc_pos hLoj n
  simp only [SOS.orbit] at hrate
  calc phi.g M - phi.g (S1.E (S1.delta^[n] pi0))
      ≤ K * (M - S1.E (S1.delta^[n] pi0)) ^ β := hlip
    _ ≤ K * ((M - S1.E pi0) / (1 + c * (M - S1.E pi0) * ↑n)) ^ β := by
        apply mul_le_mul_of_nonneg_left _ hK
        exact Real.rpow_le_rpow hgap_nn hrate (le_of_lt hβ)

/-- **Local Hölder rate transfer for α = 2**: basin-restricted version. -/
theorem SOS.Morphism.local_holder_rate_transfer_alpha2 {S1 S2 : SOS}
    (phi : SOS.Morphism S1 S2) (pi0 : S1.Pi)
    {B : Set S1.Pi} (hB : S1.IsBasin B) (h0 : pi0 ∈ B)
    {M : ℝ} (hM : ∀ π ∈ B, S1.E π ≤ M)
    {c : ℝ} (hc_pos : 0 < c)
    (hLoj : ∀ π ∈ B, S1.E (S1.delta π) - S1.E π ≥ c * (M - S1.E π) ^ 2)
    {K : ℝ} (hK : 0 ≤ K) {β : ℝ} (hβ : 0 < β)
    (hg_holder : ∀ x y : ℝ, x ≤ y → phi.g y - phi.g x ≤ K * (y - x) ^ β)
    (n : ℕ) :
    phi.g M - S2.orbit (phi.f pi0) n ≤
    K * ((M - S1.E pi0) / (1 + c * (M - S1.E pi0) * ↑n)) ^ β := by
  rw [phi.orbit_eq pi0 n]
  simp only [SOS.orbit]
  have hgap_nn : 0 ≤ M - S1.E (S1.delta^[n] pi0) := by
    linarith [hM _ (S1.iterate_mem_basin hB h0 n)]
  have hlip := hg_holder (S1.E (S1.delta^[n] pi0)) M
    (hM _ (S1.iterate_mem_basin hB h0 n))
  have hrate := S1.local_power_law_rate_alpha2 pi0 hB h0 hM hc_pos hLoj n
  simp only [SOS.orbit] at hrate
  calc phi.g M - phi.g (S1.E (S1.delta^[n] pi0))
      ≤ K * (M - S1.E (S1.delta^[n] pi0)) ^ β := hlip
    _ ≤ K * ((M - S1.E pi0) / (1 + c * (M - S1.E pi0) * ↑n)) ^ β := by
        apply mul_le_mul_of_nonneg_left _ hK
        exact Real.rpow_le_rpow hgap_nn hrate (le_of_lt hβ)

/-! ## Phase 3: General Power-Law Rate for α ≥ 2

For general α ≥ 2 (parameterised by p = α - 1 ≥ 1), the Łojasiewicz
condition E(δ(π)) - E(π) ≥ c · (M - E(π))^{p+1} gives a sublinear rate
on the p-th power of the gap:
  (M - orbit(n))^p ≤ e₀^p / (1 + c·p·e₀^p·n)

This recovers the α = 2 (p = 1) result and generalises to all integer
exponents.  The proof uses a Bernoulli-type product inequality
(1 + p·t)·(1 - t)^p ≤ 1, proved by natural-number induction. -/

/-- **Bernoulli product inequality**: (1 + p·t)·(1 - t)^p ≤ 1 for
    natural p and 0 ≤ t ≤ 1.  Key algebraic ingredient for the general
    power-law convergence rate. -/
lemma bernoulli_product (p : ℕ) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 + ↑p * t) * (1 - t) ^ p ≤ 1 := by
  induction p with
  | zero => simp
  | succ p ih =>
    have h1t : 0 ≤ 1 - t := by linarith
    -- Decompose: (1 + (p+1)t)(1-t)^{p+1}
    --          = (1-t)·(1+pt)(1-t)^p + t·(1-t)^{p+1}
    have hfact : (1 + ↑(p + 1) * t) * (1 - t) ^ (p + 1) =
        (1 - t) * ((1 + ↑p * t) * (1 - t) ^ p) +
        t * (1 - t) ^ (p + 1) := by
      simp only [Nat.cast_succ, pow_succ]
      ring
    rw [hfact]
    have h1 : (1 - t) * ((1 + ↑p * t) * (1 - t) ^ p) ≤ 1 - t := by
      calc (1 - t) * ((1 + ↑p * t) * (1 - t) ^ p)
          ≤ (1 - t) * 1 := mul_le_mul_of_nonneg_left ih h1t
        _ = 1 - t := mul_one _
    have h2 : t * (1 - t) ^ (p + 1) ≤ t := by
      calc t * (1 - t) ^ (p + 1)
          ≤ t * 1 := mul_le_mul_of_nonneg_left (pow_le_one₀ h1t (by linarith)) ht0
        _ = t := mul_one _
    linarith

/-- **General power-law rate** (multiplication form): under the
    Łojasiewicz condition with exponent p + 1 (i.e., α = p + 1 ≥ 2),
    the p-th power of the gap satisfies
    (M - orbit(n))^p · (1 + c·p·e₀^p·n) ≤ e₀^p. -/
theorem SOS.power_law_mul_general (S : SOS) (pi0 : S.Pi) (p : ℕ) (hp : 1 ≤ p)
    {M : ℝ} (hM : ∀ π : S.Pi, S.E π ≤ M)
    {c : ℝ} (hc_pos : 0 < c)
    (hLoj : ∀ π : S.Pi, S.E (S.delta π) - S.E π ≥ c * (M - S.E π) ^ (p + 1))
    (n : ℕ) :
    (M - S.orbit pi0 n) ^ p * (1 + c * ↑p * (M - S.E pi0) ^ p * ↑n) ≤
    (M - S.E pi0) ^ p := by
  set e0 := M - S.E pi0 with he0_def
  set ρ := e0 ^ p with hρ_def
  have he0_nn : 0 ≤ e0 := by linarith [hM pi0]
  have hρ_nn : 0 ≤ ρ := pow_nonneg he0_nn p
  have hc_small : c * e0 ^ p ≤ 1 := S.loj_implies_small pi0 p hp hM hc_pos hLoj
  induction n with
  | zero =>
    simp only [SOS.orbit, Function.iterate_zero, id_eq, Nat.cast_zero, mul_zero, add_zero,
               mul_one]
    exact le_refl _
  | succ n ih =>
    set en := M - S.orbit pi0 n
    have hen_nn : 0 ≤ en := S.gap_nonneg pi0 hM n
    have hen_le : en ≤ e0 := S.gap_le_initial pi0 hM n
    have henp_le : en ^ p ≤ ρ := pow_le_pow_left₀ hen_nn hen_le p
    have hcenp_le : c * en ^ p ≤ 1 :=
      le_trans (mul_le_mul_of_nonneg_left henp_le (le_of_lt hc_pos)) hc_small
    have hcenp_nn : (0 : ℝ) ≤ c * en ^ p := by positivity
    have h1cenp_nn : 0 ≤ 1 - c * en ^ p := by linarith
    -- Step: e_{n+1} ≤ en * (1 - c * en^p) from Łojasiewicz
    have hstep : M - S.orbit pi0 (n + 1) ≤ en * (1 - c * en ^ p) := by
      have hLoj_step : M - S.orbit pi0 (n + 1) ≤ en - c * en ^ (p + 1) := by
        change M - S.orbit pi0 (n + 1) ≤
          (M - S.orbit pi0 n) - c * (M - S.orbit pi0 n) ^ (p + 1)
        simp only [SOS.orbit, Function.iterate_succ', Function.comp_apply]
        linarith [hLoj (S.delta^[n] pi0)]
      have hfactor : en - c * en ^ (p + 1) = en * (1 - c * en ^ p) := by
        rw [pow_succ]; ring
      linarith
    -- Raise to p-th power
    have horbp : (M - S.orbit pi0 (n + 1)) ^ p ≤ en ^ p * (1 - c * en ^ p) ^ p := by
      have h := pow_le_pow_left₀ (S.gap_nonneg pi0 hM (n + 1)) hstep p
      rwa [mul_pow] at h
    -- Normalize ↑(n+1) to ↑n + 1
    simp only [Nat.cast_succ]
    have hden_nn : 0 ≤ 1 + c * ↑p * ρ * (↑n + 1) := by positivity
    -- Main calc chain
    calc (M - S.orbit pi0 (n + 1)) ^ p * (1 + c * ↑p * ρ * (↑n + 1))
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

/-- **General power-law rate** (division form): the p-th power of the
    gap decays as O(1/n):
    (M - orbit(n))^p ≤ e₀^p / (1 + c·p·e₀^p·n). -/
theorem SOS.power_law_rate_general (S : SOS) (pi0 : S.Pi) (p : ℕ) (hp : 1 ≤ p)
    {M : ℝ} (hM : ∀ π : S.Pi, S.E π ≤ M)
    {c : ℝ} (hc_pos : 0 < c)
    (hLoj : ∀ π : S.Pi, S.E (S.delta π) - S.E π ≥ c * (M - S.E π) ^ (p + 1))
    (n : ℕ) :
    (M - S.orbit pi0 n) ^ p ≤
    (M - S.E pi0) ^ p / (1 + c * ↑p * (M - S.E pi0) ^ p * ↑n) := by
  have he0_nn : 0 ≤ M - S.E pi0 := by linarith [hM pi0]
  have hden_pos : 0 < 1 + c * ↑p * (M - S.E pi0) ^ p * ↑n := by positivity
  rw [le_div_iff₀ hden_pos]
  exact S.power_law_mul_general pi0 p hp hM hc_pos hLoj n

/-! ## Hölder Rate Transfer for General α

Extends the α = 2 Hölder transfer to general α = p + 1 ≥ 2.
If φ : S₁ → S₂ is a morphism with g being (K, β)-Hölder continuous
and S₁ has Łojasiewicz exponent p + 1, the image orbit decays as
O(n^{-β/p}).  The proof converts between ℕ-power and ℝ-rpow via
`rpow_natCast`, then applies `rpow_le_rpow` and `rpow_mul`. -/

/-- **Hölder rate transfer for general α**: if φ.g is (K, β)-Hölder and
    S₁ has Łojasiewicz exponent p + 1, the image orbit satisfies
    g(M) - S₂.orbit(n) ≤ K · (e₀^p / (1 + c·p·e₀^p·n))^{β/p}.
    This generalises `holder_rate_transfer_alpha2` (p = 1). -/
theorem SOS.Morphism.holder_rate_transfer_general {S1 S2 : SOS}
    (phi : SOS.Morphism S1 S2) (pi0 : S1.Pi) (p : ℕ) (hp : 1 ≤ p)
    {M : ℝ} (hM : ∀ π : S1.Pi, S1.E π ≤ M)
    {c : ℝ} (hc_pos : 0 < c)
    (hLoj : ∀ π : S1.Pi, S1.E (S1.delta π) - S1.E π ≥ c * (M - S1.E π) ^ (p + 1))
    {K : ℝ} (hK : 0 ≤ K) {β : ℝ} (hβ : 0 < β)
    (hg_holder : ∀ x y : ℝ, x ≤ y → phi.g y - phi.g x ≤ K * (y - x) ^ β)
    (n : ℕ) :
    phi.g M - S2.orbit (phi.f pi0) n ≤
    K * ((M - S1.E pi0) ^ p / (1 + c * ↑p * (M - S1.E pi0) ^ p * ↑n)) ^ (β / ↑p) := by
  rw [phi.orbit_eq pi0 n]
  simp only [SOS.orbit]
  set gap := M - S1.E (S1.delta^[n] pi0)
  have hgap_nn : 0 ≤ gap := by linarith [hM (S1.delta^[n] pi0)]
  have hHolder := hg_holder (S1.E (S1.delta^[n] pi0)) M (hM (S1.delta^[n] pi0))
  have hrate := S1.power_law_rate_general pi0 p hp hM hc_pos hLoj n
  simp only [SOS.orbit] at hrate
  -- hrate : gap ^ p ≤ X where X = e₀^p / (1 + c·p·e₀^p·n)
  set X := (M - S1.E pi0) ^ p / (1 + c * ↑p * (M - S1.E pi0) ^ p * ↑n)
  have he0_nn : 0 ≤ M - S1.E pi0 := by linarith [hM pi0]
  have hX_nn : 0 ≤ X := div_nonneg (pow_nonneg he0_nn p) (by positivity)
  have hp_pos : (0 : ℝ) < ↑p := Nat.cast_pos.mpr (by omega)
  have hβp_nn : 0 ≤ β / ↑p := div_nonneg (le_of_lt hβ) (le_of_lt hp_pos)
  have hgap_p_nn : 0 ≤ gap ^ p := pow_nonneg hgap_nn p
  -- Key: gap^β = (gap^(↑p))^(β/↑p) = (gap^p)^(β/↑p) ≤ X^(β/↑p)
  have h_rpow_eq : (gap ^ p : ℝ) = gap ^ (↑p : ℝ) := (Real.rpow_natCast gap p).symm
  have h_exp_eq : gap ^ β = (gap ^ (↑p : ℝ)) ^ (β / ↑p) := by
    rw [← Real.rpow_mul hgap_nn]; congr 1; field_simp
  have h_key : gap ^ β ≤ X ^ (β / ↑p) := by
    rw [h_exp_eq, ← h_rpow_eq]
    exact Real.rpow_le_rpow hgap_p_nn hrate hβp_nn
  calc phi.g M - phi.g (S1.E (S1.delta^[n] pi0))
      ≤ K * gap ^ β := hHolder
    _ ≤ K * X ^ (β / ↑p) := mul_le_mul_of_nonneg_left h_key hK

/-! # Phase 2: Gradient Descent as a Concrete Sacred Object System

Gradient descent on L-smooth convex functions satisfies all three SOS
axioms.  The descent lemma provides Monotone Improvement.  The quadratic
Łojasiewicz condition (α = 2) follows from convexity + gradient lower bound.

The descent property is a hypothesis parameter to the construction—
analogous to how the EM inequality is a parameter to emSOS.

SOS encoding:
  Π = X  with metric structure
  E(x) = −f(x)  (negate to fit SOS maximisation convention)
  δ(x) = gdStep(x)  (e.g., x − (1/L)∇f(x))
  C = ⊤  (unconstrained) -/

section GradientDescent

/-- **Gradient Descent as a concrete SOS**: constructed from the
    descent property f(δ(x)) ≤ f(x) and a step bound.
    No `axiom` declarations — all properties are hypothesis parameters. -/
noncomputable def gradientDescentSOS
    {X : Type*} [MetricSpace X]
    (f : X → ℝ) (gdStep : X → X)
    (hf_bddBelow : BddAbove (Set.range (fun x => -f x)))
    (hDescent : ∀ x, f (gdStep x) ≤ f x)
    (D : ℝ) (hD : D > 0)
    (hStep_bdd : ∀ x, dist (gdStep x) x ≤ D) : SOS where
  Pi := X
  E := fun x => -f x
  E_bddAbove := hf_bddBelow
  Delta := D
  Delta_pos := hD
  C := fun _ => True
  delta := gdStep
  monotone_improvement := fun x => by
    simp only [ge_iff_le, neg_le_neg_iff]
    exact hDescent x
  bounded_step := hStep_bdd
  constraint_preservation := fun _ _ => trivial

/-- GD convergence: free theorem from the SOS construction. -/
theorem gd_convergence
    {X : Type*} [MetricSpace X]
    (f : X → ℝ) (gdStep : X → X)
    (hf_bddBelow : BddAbove (Set.range (fun x => -f x)))
    (hDescent : ∀ x, f (gdStep x) ≤ f x)
    (D : ℝ) (hD : D > 0)
    (hStep_bdd : ∀ x, dist (gdStep x) x ≤ D)
    (x0 : X) :
    ∃ L : ℝ, Filter.Tendsto
      ((gradientDescentSOS f gdStep hf_bddBelow hDescent D hD hStep_bdd).orbit x0)
      Filter.atTop (nhds L) :=
  (gradientDescentSOS f gdStep hf_bddBelow hDescent D hD hStep_bdd).convergence x0

/-- **GD convergence rate**: if GD additionally satisfies a quadratic
    Łojasiewicz condition (which holds for convex f with bounded level sets),
    the evaluator gap decays as O(1/n).  One-line application of
    `power_law_rate_alpha2` to the GD-SOS construction. -/
theorem gd_rate
    {X : Type*} [MetricSpace X]
    (f : X → ℝ) (gdStep : X → X)
    (hf_bddBelow : BddAbove (Set.range (fun x => -f x)))
    (hDescent : ∀ x, f (gdStep x) ≤ f x)
    (D : ℝ) (hD : D > 0)
    (hStep_bdd : ∀ x, dist (gdStep x) x ≤ D)
    {Mval : ℝ} (hM : ∀ x : X, -f x ≤ Mval)
    {c : ℝ} (hc_pos : 0 < c)
    (x0 : X)
    (hLoj : ∀ x : X, -f (gdStep x) - (-f x) ≥ c * (Mval - (-f x)) ^ 2)
    (n : ℕ) :
    Mval - (gradientDescentSOS f gdStep hf_bddBelow hDescent D hD hStep_bdd).orbit x0 n ≤
    (Mval - (-f x0)) / (1 + c * (Mval - (-f x0)) * ↑n) :=
  (gradientDescentSOS f gdStep hf_bddBelow hDescent D hD hStep_bdd).power_law_rate_alpha2
    x0 hM hc_pos hLoj n

end GradientDescent
