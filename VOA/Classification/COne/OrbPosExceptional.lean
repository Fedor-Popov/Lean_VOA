import VOA.Classification.COne.OrbPosLowest
import VOA.Classification.COne.ExceptionalOrbifoldNice

/-!
# Explicit residuals for exceptional positive weights (B5)

The two propositions below remain unproved. The spectrum assertion is the
numerical consequence of twisted-sector completeness and the cyclic lattice
module description; zero-weight identification is a separate obligation.
Sources: Dong--Ren--Xu, arXiv:1507.03306v2, Theorem 3.3 and Corollary 3.5;
Gannon--Rayhaun, arXiv:2609.00122, Proposition 3.2 and Appendix A.3.
The group orders of cyclic sectors are at most five. This does not assert
that order four occurs for A4 or A5.
-/

namespace VOA.Classification.COne.OrbPos
open VOA VertexOperatorAlgebra

/-- Residual sector-spectrum theorem, retaining strong rationality. Every
realized lowest weight has the shape of a weight of a module for `V_{2n²}`,
where `1 ≤ n ≤ 5`. This is stronger than mere nonnegativity and does not
identify which irreducible has weight zero. -/
def ExceptionalLowestWeightSpectrum : Prop :=
  ∀ (G : Subgroup (Aut (V2m 1 le_rfl))), IsExceptionalV2Group G →
    StronglyRational (orbifoldVOA G) →
    ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (N : OrdVModule (orbifoldVOA G) M),
      N.IsIrreducible → ∀ h : ℂ, IsLowestWeight N h → N.weight h ≠ ⊥ →
      ∃ (n : ℕ) (j : ℤ) (r : ℕ), 0 < n ∧ n ≤ 5 ∧ h = CyclicWeight n j r

/-- Residual vacuum identification. A realized weight zero in an irreducible
ordinary module singles out the adjoint module. No assumption of positive
weights is built into this proposition. -/
def ExceptionalZeroWeightVacuum : Prop :=
  ∀ (G : Subgroup (Aut (V2m 1 le_rfl))), IsExceptionalV2Group G →
    StronglyRational (orbifoldVOA G) →
    ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (N : OrdVModule (orbifoldVOA G) M),
      N.IsIrreducible → N.weight 0 ≠ ⊥ →
      Nonempty (ModuleEquiv (orbifoldVOA G) N (adjointModule (orbifoldVOA G)))

/-- Quantitative endpoint of the sector route: every weight in every
non-vacuum irreducible module is at least `1/100`. Both residuals are explicit. -/
theorem exceptional_weights_gap_of_residuals
    (hs : ExceptionalLowestWeightSpectrum) (hz : ExceptionalZeroWeightVacuum)
    (G : Subgroup (Aut (V2m 1 le_rfl))) (hG : IsExceptionalV2Group G)
    (hSR : StronglyRational (orbifoldVOA G))
    (M : Type) [AddCommGroup M] [Module ℂ M] (N : OrdVModule (orbifoldVOA G) M)
    (hi : N.IsIrreducible)
    (hn : IsEmpty (ModuleEquiv (orbifoldVOA G) N (adjointModule (orbifoldVOA G))))
    (α : ℂ) (hα : N.weight α ≠ ⊥) : (1 : ℝ) / 100 ≤ α.re := by
  obtain ⟨h, hl, hh⟩ := N.exists_isLowestWeight_of_irreducible hi
  have hne : h ≠ 0 := by
    intro h0
    obtain ⟨e⟩ := hz G hG hSR M N hi (h0 ▸ hh)
    exact hn.false e
  obtain ⟨n, j, r, hn0, hn5, he⟩ := hs G hG hSR M N hi h hl hh
  have hgap := cyclicWeight_gap hn0 hn5 j r (he ▸ hne)
  have hgap' : (1 : ℝ) / 100 ≤ h.re := by norm_num [← he] at hgap ⊢; exact hgap
  obtain ⟨k, rfl⟩ := hl α hα
  simp only [Complex.add_re, Complex.natCast_re]
  exact hgap'.trans (le_add_of_nonneg_right k.cast_nonneg)

/-- The original B5 target, conditional on exactly the two displayed residuals. -/
theorem exceptionalOrbifoldPositiveWeightsFact_of_residuals
    (hs : ExceptionalLowestWeightSpectrum) (hz : ExceptionalZeroWeightVacuum) :
    ExceptionalOrbifoldPositiveWeightsFact := by
  intro G hG hSR M _ _ N hi hn α hα
  exact lt_of_lt_of_le (by norm_num)
    (exceptional_weights_gap_of_residuals hs hz G hG hSR M N hi hn α hα)

/-- The zero-weight residual is necessary for B5; it is not an extra
positivity assumption hidden inside the spectrum assertion. -/
theorem exceptionalZeroWeightVacuum_of_positiveWeights
    (hp : ExceptionalOrbifoldPositiveWeightsFact) : ExceptionalZeroWeightVacuum := by
  intro G hG hSR M _ _ N hi hh
  by_contra he
  have hn : IsEmpty (ModuleEquiv (orbifoldVOA G) N (adjointModule (orbifoldVOA G))) :=
    ⟨fun e => he ⟨e⟩⟩
  have := hp G hG hSR M N hi hn 0 hh
  simpa using this

/-- Under the concrete spectrum theorem, the only remaining logical condition
for B5 is identification of the zero-weight vacuum. -/
theorem exceptional_positiveWeights_iff_zeroWeightVacuum
    (hs : ExceptionalLowestWeightSpectrum) :
    ExceptionalOrbifoldPositiveWeightsFact ↔ ExceptionalZeroWeightVacuum :=
  ⟨exceptionalZeroWeightVacuum_of_positiveWeights,
    exceptionalOrbifoldPositiveWeightsFact_of_residuals hs⟩

end VOA.Classification.COne.OrbPos
