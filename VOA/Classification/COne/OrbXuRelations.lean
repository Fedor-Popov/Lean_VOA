import VOA.Classification.COne.OrbXuSpan
import VOA.Classification.COne.OrbXuBinary

/-!
# Statement check and an exact state-level interface for B4

`XuIcosahedralPoissonRelations` matches Xu arXiv:2608.13872v2, Theorem 6.4,
Lemma 7.5 and Proposition 7.7. The degree-6 harmonic invariant corresponds
to the degree-12 binary form and hence a primary of conformal weight 36.
The invariant generators of degrees 10 and 15 do not contradict two towers:
Xu first obtains four towers, then eliminates their classes by the modes
`X₋₂₉X` and `X₋₉₀Y`. The latter has weight 225; its lower channel levels
189, 125 and 81 are odd. The former has weight 100; the remaining levels
100 and 64 give powers 50 and 32 of the conformal class.

The equivalence below keeps every original condition, including the same
nonzero couplings at both weights. It is a reformulation, not a proof of B4.
`OrbXuBinary` proves the four small polynomial channel identities and Klein's
relation. The missing representation-theoretic bridge must still identify
these projections with nonzero VOA channel coefficients.

## Work still required

* A standard form for an arbitrary embedded A₅, or a conjugacy-free invariant
  calculation. The normal-Klein-four argument used for A₄/S₄ does not apply
  to A₅, whose Klein four subgroups are not normal.
* The A₅ invariant-ring generation theorem and its homogeneous version,
  followed by the two non-top channel eliminations. `OrbPrim.PrimModel`
  has A₄-specific invariant fields and cannot be instantiated unchanged.
* The scalar-symbol/VOA bridge for R1/R2. Reproducing rational constants alone
  cannot supply this bridge.

## Size estimates and the preferred route to R1/R2

From the rank-one character formula, the dimensions of V₂ at weights 74 and
76 are 33,495,450 and 44,164,233. Even the unrestricted vacuum PBW levels have
7,089,500 and 9,289,091 partitions. These are estimates of ambient calculation
size, not a lower bound on sparse support. At weights 100 and 225 the lattice
dimensions are 966,806,298 and 196,849,047,376,283. Full state expansion is
therefore not a reasonable way to implement either channel elimination.

Xu's alternative is a level-13 null-vector equation and a width-six scalar
recurrence. There are only 4096 ordered compositions of 13, and only indices
through 38 (vacuum) and 20 (self) are needed. A dynamic program can reuse
composition suffixes. However, specialization at t=1 has vacuum resonances
2,8,18,32 and a self resonance 14. The regularized family and its identification
with the genuine intertwining coefficients must be proved; a recurrence
that simply divides by its specialized leading coefficient is invalid there.

No large VOA computation was attempted in these files.
-/

set_option Elab.async false

noncomputable section
namespace VOA.Classification.COne.OrbXu
open VOA VertexOperatorAlgebra OrbSpan

universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V]

/-- A state-level symbol remainder; no quotient or implicit channel projection. -/
def modeSymbol (W : VertexOperatorAlgebra V) (X : V) (m : ℤ)
    (p q : ℕ) (a b : ℂ) : V :=
  W.smul X m X - a • (W.L (-2) ^ p) W.vacuum - b • (W.L (-2) ^ q) X

/-- For a mode in C₂, the state remainder is precisely the desired quotient relation. -/
theorem modeSymbol_mem_iff (W : VertexOperatorAlgebra V) (X : V) {m : ℤ}
    (hm : m ≤ -2) (p q : ℕ) (a b : ℂ) :
    modeSymbol W X m p q a b ∈ O₂ W ↔
      a • (exceptionalConformalEnd W ^ p) (mk₂ W W.vacuum) +
        b • (exceptionalConformalEnd W ^ q) (mk₂ W X) = 0 := by
  have hz : mk₂ W (W.smul X m X) = 0 :=
    (mk₂_eq_zero_iff W).mpr (smul_le_neg_two_mem_O₂ W X X hm)
  rw [← mk₂_eq_zero_iff W, modeSymbol, map_sub, map_sub, map_smul, map_smul, hz,
    ← exceptionalConformalEnd_pow_mk, ← exceptionalConformalEnd_pow_mk]
  rw [zero_sub, sub_eq_add_neg, ← neg_add, neg_eq_zero]

/-- An OPEN state-level version of B4, proved equivalent to the original below.
This definition is not an assertion that the indicated witnesses exist. -/
def XuIcosahedralPrimaryAndSymbols : Prop :=
  ∀ (G : Subgroup (Aut (V2m 1 le_rfl))), Nonempty (G ≃* alternatingGroup (Fin 5)) →
    ∃ (X : (orbifold G).carrier) (c₀ c₆ : ℂ),
      X ∈ (orbifoldVOA G).grading 36 ∧ c₀ ≠ 0 ∧ c₆ ≠ 0 ∧
      PrimaryC2Reduction (orbifoldVOA G) {(orbifoldVOA G).vacuum, X} ∧
      modeSymbol (orbifoldVOA G) X (-3) 37 19
        (c₀ * (xuU37 : ℂ)) (c₆ * (xuV19 : ℂ)) ∈ O₂ (orbifoldVOA G) ∧
      modeSymbol (orbifoldVOA G) X (-5) 38 20
        (c₀ * (xuU38 : ℂ)) (c₆ * (xuV20 : ℂ)) ∈ O₂ (orbifoldVOA G)

-- Comparing the two quotient-power expressions needs a deeper definitional stack.
set_option maxRecDepth 4096 in
/-- Exact reformulation: no spanning condition, coefficient or nonvanishing is dropped. -/
theorem xuIcosahedralPoissonRelations_iff_primaryAndSymbols :
    XuIcosahedralPoissonRelations ↔ XuIcosahedralPrimaryAndSymbols := by
  constructor
  · intro h G hG
    obtain ⟨X, c₀, c₆, hX, hc₀, hc₆, hs, h74, h76⟩ := h G hG
    exact ⟨X, c₀, c₆, hX, hc₀, hc₆,
      (orbifold_twoTowers_iff_primary G hX).mp hs,
      (modeSymbol_mem_iff _ X (by norm_num : (-3 : ℤ) ≤ -2) _ _ _ _).mpr h74,
      (modeSymbol_mem_iff _ X (by norm_num : (-5 : ℤ) ≤ -2) _ _ _ _).mpr h76⟩
  · intro h G hG
    obtain ⟨X, c₀, c₆, hX, hc₀, hc₆, hp, h74, h76⟩ := h G hG
    exact ⟨X, c₀, c₆, hX, hc₀, hc₆,
      (orbifold_twoTowers_iff_primary G hX).mpr hp,
      (modeSymbol_mem_iff _ X (by norm_num : (-3 : ℤ) ≤ -2) _ _ _ _).mp h74,
      (modeSymbol_mem_iff _ X (by norm_num : (-5 : ℤ) ≤ -2) _ _ _ _).mp h76⟩

/-- The state-level interface implies the existing C₂-cofiniteness conclusion. -/
theorem icosa_c2_of_primaryAndSymbols (h : XuIcosahedralPrimaryAndSymbols)
    (G : Subgroup (Aut (V2m 1 le_rfl))) (hG : Nonempty (G ≃* alternatingGroup (Fin 5))) :
    C2Cofinite (orbifoldVOA G) ∧ Module.finrank ℂ (A₂ (orbifoldVOA G)) ≤ 58 :=
  exceptionalOrbifold_icosa_c2_of_relations
    (xuIcosahedralPoissonRelations_iff_primaryAndSymbols.mpr h) G hG

end VOA.Classification.COne.OrbXu
