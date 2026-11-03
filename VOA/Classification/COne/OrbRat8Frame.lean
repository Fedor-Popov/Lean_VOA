/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.OrbRat7Assembly

/-!
# Non-vacuum resonant pairs: reduction to top vectors of cyclic modules

General `C₂`-cofinite VOA `W`, two-step extension `0 → P → A → A/P → 0` with simple kernel of
bottom `hk` and simple quotient of bottom `hq`, `Re hq < Re hk` (the kernel sits above).

* `pairSplit_of_topCyclicVanishing`: the extension splits as soon as `TopCyclicVanishing W hq hk`
  holds: in every weak module with no generalized weights below `Re hq`, a top vector `v` of
  weight `hk` lying in the cyclic submodule of a top vector `u` of weight `hq` vanishes.
  Proof: the quotient bottom lifts to an eigenvector `u ∉ P` (`exists_eigen_lift`), which is a
  top vector; if `P ⊓ cyclic u ≠ ⊥` then `P ≤ cyclic u` (atom), and an `L(0)`-eigenvector `v` of
  `P` at `hk` is a top vector in `cyclic u`, hence `0` — impossible.
* For the tetrahedral model, `CubicNonVacuumPairs` follows from the two instances
  `TopCyclicVanishing cubicModel 1 4` and `TopCyclicVanishing cubicModel (1/4) (9/4)`
  (`cubicNonVacuumPairs_of_topCyclic`), and rationality-from-`C₂` from those plus
  `CubicZhuDimensionBound` (`cubicModelRationalOfC2_of_topCyclic`).

The residual `TopCyclicVanishing` is the statement "the universal module over a top of weight
`hq` has no top vector at weight `hk`"; it does not mention extensions.  It is open for the
tetrahedral model.
-/

set_option maxSynthPendingDepth 3

noncomputable section

namespace VOA.Classification.COne.OrbRat8

open VOA VertexOperatorAlgebra PlusSplitting PlusRational ABDWeakAdmissible
  VOA.Huang.LogRemovalAdmissible

universe u

section Generic

variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}

/-- OPEN residual (for the tetrahedral model): in a weak module with no generalized weights of
real part below `Re hq`, a top vector of weight `hk` inside the cyclic submodule of a top vector
of weight `hq` is zero. -/
def TopCyclicVanishing (W : VertexOperatorAlgebra V) (hq hk : ℂ) : Prop :=
  ∀ {M : Type u} [AddCommGroup M] [Module ℂ M] (A : WeakModule W M) (u v : M),
    u ∈ Omega A → L0 A u = hq • u →
    (∀ μ : ℂ, μ.re < hq.re → ∀ y ∈ (L0 A).maxGenEigenspace μ, y = 0) →
    v ∈ Omega A → L0 A v = hk • v → v ∈ PlusRational.cyclic A u → v = 0

variable {M : Type u} [AddCommGroup M] [Module ℂ M]

/-- No generalized weight lies below the quotient bottom when the kernel bottom is higher. -/
theorem low_weights_vanish (A : WeakModule W M) {P : Submodule (modeAlg A) M} {hq hk : ℂ}
    (hlt : hq.re < hk.re) (hb : FactorBottom A ⊥ P hk) (ht : FactorBottom A P ⊤ hq) :
    ∀ μ : ℂ, μ.re < hq.re → ∀ y ∈ (L0 A).maxGenEigenspace μ, y = 0 := by
  intro μ hμ y hy
  have hyP : y ∈ P := by
    by_contra hc
    have hw : FactorWeight A P ⊤ μ := fun hT => hc (hT ⟨Submodule.mem_top, hy⟩)
    have := ht.2 μ hw
    linarith
  exact kernel_generalized_below_bottom_eq_zero A P _ hb hyP hy (by linarith)

/-- An eigenvector of `L(0)` with no generalized weights below it is a top vector. -/
theorem mem_Omega_of_low (A : WeakModule W M) {hq : ℂ}
    (hlow : ∀ μ : ℂ, μ.re < hq.re → ∀ y ∈ (L0 A).maxGenEigenspace μ, y = 0)
    {x : M} (hxL : L0 A x = hq • x) : x ∈ Omega A := by
  have hxg : x ∈ (L0 A).maxGenEigenspace hq :=
    Module.End.eigenspace_le_maxGenEigenspace (Module.End.mem_eigenspace_iff.mpr hxL)
  intro β v hv n hn
  apply hlow _ _ _ (mode_mem_maxGenEigenspace A hv n hxg)
  have : ((β - n - 1 : ℤ) : ℝ) ≤ -1 := by exact_mod_cast (show β - n - 1 ≤ -1 by omega)
  rw [Complex.add_re, Complex.intCast_re]
  linarith

/-- A nonzero generalized eigenvector inside a mode submodule yields an honest eigenvector in
the same submodule. -/
theorem exists_eigen_in_submodule (A : WeakModule W M) (P : Submodule (modeAlg A) M)
    {h : ℂ} {y : M} (hyP : y ∈ P) (hy : y ∈ (L0 A).maxGenEigenspace h) (hy0 : y ≠ 0) :
    ∃ v : M, v ∈ P ∧ v ≠ 0 ∧ L0 A v = h • v := by
  classical
  obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).mp hy
  set f := L0 A - h • (1 : Module.End ℂ M) with hfdef
  have hfP : ∀ z ∈ P, f z ∈ P := by
    intro z hz
    have h1 : L0 A z ∈ P := (ofR A P).act_mem W.conformalVector 1 hz
    have h2 : f z = L0 A z - h • z := by
      simp [hfdef]
    rw [h2]
    exact P.sub_mem h1 (P.smul_mem (algebraMap ℂ (modeAlg A) h) hz)
  have hpowP : ∀ j : ℕ, (f ^ j) y ∈ P := by
    intro j
    induction j with
    | zero => simpa using hyP
    | succ j ih =>
      rw [pow_succ', Module.End.mul_apply]
      exact hfP _ ih
  have hex : ∃ j : ℕ, (f ^ (j + 1)) y = 0 := ⟨k, by
    rw [show k + 1 = 1 + k by ring, pow_add, Module.End.mul_apply, hk, map_zero]⟩
  let jj := Nat.find hex
  have hjf : (f ^ (jj + 1)) y = 0 := Nat.find_spec hex
  have hj0 : (f ^ jj) y ≠ 0 := by
    rcases Nat.eq_zero_or_pos jj with hz | hz
    · rw [hz, pow_zero]; exact hy0
    · have := Nat.find_min hex (show jj - 1 < jj by omega)
      rwa [Nat.sub_add_cancel hz] at this
  refine ⟨(f ^ jj) y, hpowP jj, hj0, ?_⟩
  have hfx : f ((f ^ jj) y) = 0 := by
    rw [← Module.End.mul_apply, ← pow_succ']; exact hjf
  have : L0 A ((f ^ jj) y) - h • (f ^ jj) y = 0 := by
    simpa [hfdef] using hfx
  exact sub_eq_zero.mp this

/-- **Reduction of a resonant pair (kernel above) to top vectors of cyclic modules.** -/
theorem pairSplit_of_topCyclicVanishing (hC2 : C2Cofinite W) {hq hk : ℂ}
    (hlt : hq.re < hk.re) (H : TopCyclicVanishing W hq hk) :
    PlusRat2Dual.PairSplit W hk hq := by
  intro M _ _ A P hP hQ hb ht
  have hne : hk ≠ hq := by
    intro h; rw [h] at hlt; exact lt_irrefl _ hlt
  obtain ⟨x, hxL, hxP⟩ := PlusRat2Dual.exists_eigen_lift hC2 A P hP hne hb ht
  have hlow := low_weights_vanish A hlt hb ht
  have hxΩ := mem_Omega_of_low A hlow hxL
  by_cases hd : Disjoint P (PlusRational.cyclic A x)
  · apply (exists_cyclic_lift_iff_complement A P hQ hq ht).mp
    refine ⟨x, ?_, hxP, hd⟩
    exact Module.End.eigenspace_le_maxGenEigenspace (Module.End.mem_eigenspace_iff.mpr hxL)
  · exfalso
    have hPle : P ≤ PlusRational.cyclic A x := by
      rcases hP.le_iff.mp (inf_le_left : P ⊓ PlusRational.cyclic A x ≤ P) with h | h
      · exact absurd (disjoint_iff.mpr h) hd
      · rw [← h]; exact inf_le_right
    -- a nonzero generalized eigenvector of `P` at `hk`
    have hw := hb.1
    unfold FactorWeight at hw
    obtain ⟨y, ⟨hyP, hyg⟩, hy0⟩ := Set.not_subset.mp hw
    have hyP' : y ∈ P := hyP
    have hy0' : y ≠ 0 := by
      intro h; apply hy0; rw [h]; exact Submodule.zero_mem _
    obtain ⟨v, hvP, hv0, hvL⟩ := exists_eigen_in_submodule A P hyP' hyg hy0'
    have hvΩ : v ∈ Omega A := kernel_bottom_mem_Omega A P hk hb hvP
      (Module.End.eigenspace_le_maxGenEigenspace (Module.End.mem_eigenspace_iff.mpr hvL))
    exact hv0 (H A x v hxΩ hxL hlow hvΩ hvL (hPle hvP))

end Generic

/-! ## The tetrahedral model -/

section Cubic

open OrbRat2

/-- OPEN: the two cyclic top-vector statements for the non-vacuum resonant pairs. -/
def CubicTopCyclicPairs : Prop :=
  TopCyclicVanishing cubicModel 1 4 ∧ TopCyclicVanishing cubicModel (1 / 4) (9 / 4)

/-- `CubicNonVacuumPairs` from the cyclic top-vector statements. -/
theorem cubicNonVacuumPairs_of_topCyclic (hC2 : C2Cofinite cubicModel)
    (h : CubicTopCyclicPairs) : CubicNonVacuumPairs :=
  ⟨pairSplit_of_topCyclicVanishing hC2 (by norm_num) h.1,
    pairSplit_of_topCyclicVanishing hC2 (by norm_num) h.2⟩

/-- Rationality-from-`C₂` of the tetrahedral model from the Zhu dimension bound and the
cyclic top-vector statements. -/
theorem cubicModelRationalOfC2_of_topCyclic (hdim : CubicZhuDimensionBound)
    (h : CubicTopCyclicPairs) : CubicModelRationalOfC2 := fun hC2 =>
  OrbRat7.cubicModelRationalOfC2_of_dim hdim (cubicNonVacuumPairs_of_topCyclic hC2 h) hC2

end Cubic

end VOA.Classification.COne.OrbRat8
