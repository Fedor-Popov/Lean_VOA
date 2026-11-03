/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import Mathlib.Data.Fintype.Vector
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Finite mode--particle pairings

This file constructs the finite coefficient pairing which underlies the restricted-dual
functional model for the boundary affine auxiliary algebra.  A commutative monomial containing
`n` divided-derivative modes is indexed by the symmetric power
`Sym (Fin (jetOrder + 1)) n`: the entries are the derivative orders and repeated entries record
repeated modes.  Fixing the symmetric power fixes particle number, and fixing `modeDegree` fixes
derivative degree.

The dual coordinate is the coefficient of the corresponding same-species symmetric labelled
particle polynomial.  Thus both sides of a fixed finite sector have the same finite basis, and
`modeParticlePairing` is the ordinary coordinate pairing.  The two nondegeneracy theorems below
make this perfectness explicit, without an unproved appeal to a restricted-dual realization.

The last section proves the coefficient form of the field-product/diagonal adjunction.  For two
different species, the coefficient of `X(z) Z(z)` inserts one `X` mode and one `Z` mode.  For one
species, the coefficient of `Y(z)^2` is the ordered convolution.  Consequently the two distinct
orders `(r,s)` and `(s,r)` give the factor `2` when `r != s`, whereas the diagonal term `r=s`
occurs once.  This is the exact factorial normalization required by the polarized relation
`X(z) Z(z) - Y(z)^2`; no scalar is hidden in an interface field.

This is a finite coefficient model.  It does not yet identify these coefficient families with a
subspace of `MvPolynomial`, identify an ideal orthogonal complement, or assert any carrier or
classical-freeness theorem.
-/

namespace VOA.ModeParticlePairing

noncomputable section

universe u

variable {K : Type u}

/-- A same-species mode monomial with `n` particles and every derivative order at most
`jetOrder`.  The symmetric power records commutativity of identical-species modes. -/
abbrev ModeConfiguration (jetOrder n : ℕ) := Sym (Fin (jetOrder + 1)) n

/-- Total derivative degree of a finite mode configuration. -/
def modeDegree {jetOrder n : ℕ} (b : ModeConfiguration jetOrder n) : ℕ :=
  ((b : Multiset (Fin (jetOrder + 1))).map Fin.val).sum

@[simp]
theorem modeDegree_nil (jetOrder : ℕ) :
    modeDegree (Sym.nil : ModeConfiguration jetOrder 0) = 0 := by
  rfl

@[simp]
theorem modeDegree_cons {jetOrder n : ℕ} (r : Fin (jetOrder + 1))
    (b : ModeConfiguration jetOrder n) :
    modeDegree (r ::ₛ b) = r + modeDegree b := by
  simp [modeDegree, Sym.coe_cons]

/-- The finite basis in fixed particle number and fixed derivative degree. -/
abbrev FixedModeConfiguration (jetOrder n derivativeDegree : ℕ) :=
  {b : ModeConfiguration jetOrder n // modeDegree b = derivativeDegree}

/-- A fixed-particle, fixed-derivative-degree mode sector.  Coordinates are coefficients of
ordinary commutative monomials in the divided-derivative generators. -/
abbrev ModeSector (K : Type u) (jetOrder n derivativeDegree : ℕ) :=
  FixedModeConfiguration jetOrder n derivativeDegree → K

/-- The matching coefficient model for same-species symmetric labelled particle polynomials.
The coordinate at `b` is the coefficient of any labelled monomial whose multiset of exponents is
`b`. -/
abbrev ParticleSector (K : Type u) (jetOrder n derivativeDegree : ℕ) :=
  FixedModeConfiguration jetOrder n derivativeDegree → K

section PerfectPairing

variable [Field K]

/-- Coordinate pairing in a fixed finite particle/derivative sector. -/
def modeParticlePairing {jetOrder n derivativeDegree : ℕ}
    (u : ModeSector K jetOrder n derivativeDegree)
    (F : ParticleSector K jetOrder n derivativeDegree) : K :=
  ∑ b, u b * F b

/-- Delta mode vector at one commutative mode configuration. -/
def deltaMode {jetOrder n derivativeDegree : ℕ}
    (b : FixedModeConfiguration jetOrder n derivativeDegree) :
    ModeSector K jetOrder n derivativeDegree :=
  fun c ↦ if c = b then 1 else 0

/-- Delta particle coefficient at one commutative mode configuration. -/
def deltaParticle {jetOrder n derivativeDegree : ℕ}
    (b : FixedModeConfiguration jetOrder n derivativeDegree) :
    ParticleSector K jetOrder n derivativeDegree :=
  fun c ↦ if c = b then 1 else 0

@[simp]
theorem modeParticlePairing_deltaMode {jetOrder n derivativeDegree : ℕ}
    (b : FixedModeConfiguration jetOrder n derivativeDegree)
    (F : ParticleSector K jetOrder n derivativeDegree) :
    modeParticlePairing (deltaMode (K := K) b) F = F b := by
  simp [modeParticlePairing, deltaMode]

@[simp]
theorem modeParticlePairing_deltaParticle {jetOrder n derivativeDegree : ℕ}
    (u : ModeSector K jetOrder n derivativeDegree)
    (b : FixedModeConfiguration jetOrder n derivativeDegree) :
    modeParticlePairing u (deltaParticle (K := K) b) = u b := by
  simp [modeParticlePairing, deltaParticle]

/-- Nondegeneracy in the mode slot of the finite mode--particle pairing. -/
theorem modeParticlePairing_left_nondegenerate {jetOrder n derivativeDegree : ℕ}
    {u : ModeSector K jetOrder n derivativeDegree}
    (h : ∀ F, modeParticlePairing u F = 0) :
    u = 0 := by
  funext b
  simpa using h (deltaParticle (K := K) b)

/-- Nondegeneracy in the particle slot of the finite mode--particle pairing. -/
theorem modeParticlePairing_right_nondegenerate {jetOrder n derivativeDegree : ℕ}
    {F : ParticleSector K jetOrder n derivativeDegree}
    (h : ∀ u, modeParticlePairing u F = 0) :
    F = 0 := by
  funext b
  simpa using h (deltaMode (K := K) b)

/-- The fixed sector is finite dimensional.  This is the finiteness needed for taking its
ordinary algebraic dual; no completion or topology is involved. -/
theorem modeSector_finiteDimensional (jetOrder n derivativeDegree : ℕ) :
    FiniteDimensional K (ModeSector K jetOrder n derivativeDegree) := by
  infer_instance

/-- The symmetric labelled-particle coefficient sector is finite dimensional as well. -/
theorem particleSector_finiteDimensional (jetOrder n derivativeDegree : ℕ) :
    FiniteDimensional K (ParticleSector K jetOrder n derivativeDegree) := by
  infer_instance

end PerfectPairing

section FixedMultidegree

variable {Species : Type*} [Fintype Species]
variable [Field K]

local instance : DecidableEq Species := Classical.decEq _

/-- A mode monomial in a fixed species multidegree.  The function `multiplicity` prescribes the
number of particles of each species. -/
abbrev MultispeciesModeConfiguration (jetOrder : ℕ) (multiplicity : Species → ℕ) :=
  ∀ A, ModeConfiguration jetOrder (multiplicity A)

/-- Total derivative degree across all species. -/
def multispeciesModeDegree {jetOrder : ℕ} {multiplicity : Species → ℕ}
    (b : MultispeciesModeConfiguration jetOrder multiplicity) : ℕ :=
  ∑ A, modeDegree (b A)

/-- The finite basis in one fixed species multidegree and one fixed derivative degree. -/
abbrev FixedMultispeciesModeConfiguration (jetOrder : ℕ)
    (multiplicity : Species → ℕ) (derivativeDegree : ℕ) :=
  {b : MultispeciesModeConfiguration jetOrder multiplicity //
    multispeciesModeDegree b = derivativeDegree}

/-- Mode coefficients in one fixed species multidegree and derivative degree. -/
abbrev MultispeciesModeSector (K : Type u) (jetOrder : ℕ)
    (multiplicity : Species → ℕ) (derivativeDegree : ℕ) :=
  FixedMultispeciesModeConfiguration jetOrder multiplicity derivativeDegree → K

/-- Same-species symmetric particle coefficients in one fixed species multidegree and derivative
degree. -/
abbrev MultispeciesParticleSector (K : Type u) (jetOrder : ℕ)
    (multiplicity : Species → ℕ) (derivativeDegree : ℕ) :=
  FixedMultispeciesModeConfiguration jetOrder multiplicity derivativeDegree → K

/-- The finite mode--particle pairing in exactly the `(multiplicity, derivativeDegree)` sector. -/
def multispeciesModeParticlePairing {jetOrder derivativeDegree : ℕ}
    {multiplicity : Species → ℕ}
    (u : MultispeciesModeSector K jetOrder multiplicity derivativeDegree)
    (F : MultispeciesParticleSector K jetOrder multiplicity derivativeDegree) : K :=
  ∑ b, u b * F b

/-- A delta mode vector in a fixed multidegree. -/
def multispeciesDeltaMode {jetOrder derivativeDegree : ℕ}
    {multiplicity : Species → ℕ}
    (b : FixedMultispeciesModeConfiguration jetOrder multiplicity derivativeDegree) :
    MultispeciesModeSector K jetOrder multiplicity derivativeDegree :=
  fun c ↦ if c = b then 1 else 0

/-- A delta particle coefficient in a fixed multidegree. -/
def multispeciesDeltaParticle {jetOrder derivativeDegree : ℕ}
    {multiplicity : Species → ℕ}
    (b : FixedMultispeciesModeConfiguration jetOrder multiplicity derivativeDegree) :
    MultispeciesParticleSector K jetOrder multiplicity derivativeDegree :=
  fun c ↦ if c = b then 1 else 0

@[simp]
theorem multispeciesModeParticlePairing_deltaMode {jetOrder derivativeDegree : ℕ}
    {multiplicity : Species → ℕ}
    (b : FixedMultispeciesModeConfiguration jetOrder multiplicity derivativeDegree)
    (F : MultispeciesParticleSector K jetOrder multiplicity derivativeDegree) :
    multispeciesModeParticlePairing (multispeciesDeltaMode (K := K) b) F = F b := by
  simp [multispeciesModeParticlePairing, multispeciesDeltaMode]

@[simp]
theorem multispeciesModeParticlePairing_deltaParticle {jetOrder derivativeDegree : ℕ}
    {multiplicity : Species → ℕ}
    (u : MultispeciesModeSector K jetOrder multiplicity derivativeDegree)
    (b : FixedMultispeciesModeConfiguration jetOrder multiplicity derivativeDegree) :
    multispeciesModeParticlePairing u (multispeciesDeltaParticle (K := K) b) = u b := by
  simp [multispeciesModeParticlePairing, multispeciesDeltaParticle]

/-- Left nondegeneracy of the exact fixed-multidegree pairing. -/
theorem multispeciesModeParticlePairing_left_nondegenerate
    {jetOrder derivativeDegree : ℕ} {multiplicity : Species → ℕ}
    {u : MultispeciesModeSector K jetOrder multiplicity derivativeDegree}
    (h : ∀ F, multispeciesModeParticlePairing u F = 0) :
    u = 0 := by
  funext b
  simpa using h (multispeciesDeltaParticle (K := K) b)

/-- Right nondegeneracy of the exact fixed-multidegree pairing. -/
theorem multispeciesModeParticlePairing_right_nondegenerate
    {jetOrder derivativeDegree : ℕ} {multiplicity : Species → ℕ}
    {F : MultispeciesParticleSector K jetOrder multiplicity derivativeDegree}
    (h : ∀ u, multispeciesModeParticlePairing u F = 0) :
    F = 0 := by
  funext b
  simpa using h (multispeciesDeltaMode (K := K) b)

/-- Fixed multidegree and derivative degree give a finite-dimensional mode sector. -/
theorem multispeciesModeSector_finiteDimensional (jetOrder derivativeDegree : ℕ)
    (multiplicity : Species → ℕ) :
    FiniteDimensional K
      (MultispeciesModeSector K jetOrder multiplicity derivativeDegree) := by
  infer_instance

/-- Fixed multidegree and derivative degree give a finite-dimensional particle sector. -/
theorem multispeciesParticleSector_finiteDimensional (jetOrder derivativeDegree : ℕ)
    (multiplicity : Species → ℕ) :
    FiniteDimensional K
      (MultispeciesParticleSector K jetOrder multiplicity derivativeDegree) := by
  infer_instance

end FixedMultidegree

section FullFiniteJetPairing

variable [Field K]

/-- The full finite-jet mode coefficient space in fixed particle number, before taking a fixed
derivative-degree summand. -/
abbrev JetModeSpace (K : Type u) (jetOrder n : ℕ) :=
  ModeConfiguration jetOrder n → K

/-- The full finite-jet symmetric particle coefficient space in fixed particle number. -/
abbrev JetParticleSpace (K : Type u) (jetOrder n : ℕ) :=
  ModeConfiguration jetOrder n → K

/-- Coordinate pairing before restriction to a derivative-degree summand. -/
def jetModeParticlePairing {jetOrder n : ℕ}
    (u : JetModeSpace K jetOrder n) (F : JetParticleSpace K jetOrder n) : K :=
  ∑ b, u b * F b

/-- Delta vector in the finite-jet mode coefficient space. -/
def jetDeltaMode {jetOrder n : ℕ} (b : ModeConfiguration jetOrder n) :
    JetModeSpace K jetOrder n :=
  fun c ↦ if c = b then 1 else 0

@[simp]
theorem jetModeParticlePairing_delta {jetOrder n : ℕ}
    (b : ModeConfiguration jetOrder n) (F : JetParticleSpace K jetOrder n) :
    jetModeParticlePairing (jetDeltaMode (K := K) b) F = F b := by
  simp [jetModeParticlePairing, jetDeltaMode]

theorem jetModeParticlePairing_add {jetOrder n : ℕ}
    (u v : JetModeSpace K jetOrder n) (F : JetParticleSpace K jetOrder n) :
    jetModeParticlePairing (u + v) F =
      jetModeParticlePairing u F + jetModeParticlePairing v F := by
  simp [jetModeParticlePairing, add_mul, Finset.sum_add_distrib]

theorem jetModeParticlePairing_sum {jetOrder n : ℕ} {I : Type*}
    (s : Finset I) (u : I → JetModeSpace K jetOrder n)
    (F : JetParticleSpace K jetOrder n) :
    jetModeParticlePairing (∑ i ∈ s, u i) F =
      ∑ i ∈ s, jetModeParticlePairing (u i) F := by
  classical
  simp only [jetModeParticlePairing, Finset.sum_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

/-- Bidegree configurations for two distinct particle species. -/
abbrev TwoSpeciesConfiguration (jetOrder a c : ℕ) :=
  ModeConfiguration jetOrder a × ModeConfiguration jetOrder c

/-- Finite-jet mode coefficients for two distinct species. -/
abbrev TwoSpeciesModeSpace (K : Type u) (jetOrder a c : ℕ) :=
  TwoSpeciesConfiguration jetOrder a c → K

/-- Finite-jet particle coefficients for two distinct species. -/
abbrev TwoSpeciesParticleSpace (K : Type u) (jetOrder a c : ℕ) :=
  TwoSpeciesConfiguration jetOrder a c → K

/-- Coordinate pairing for two distinct species. -/
def twoSpeciesPairing {jetOrder a c : ℕ}
    (u : TwoSpeciesModeSpace K jetOrder a c)
    (F : TwoSpeciesParticleSpace K jetOrder a c) : K :=
  ∑ b, u b * F b

/-- Delta vector at one pair of distinct-species mode configurations. -/
def twoSpeciesDeltaMode {jetOrder a c : ℕ}
    (b : TwoSpeciesConfiguration jetOrder a c) :
    TwoSpeciesModeSpace K jetOrder a c :=
  fun d ↦ if d = b then 1 else 0

@[simp]
theorem twoSpeciesPairing_delta {jetOrder a c : ℕ}
    (b : TwoSpeciesConfiguration jetOrder a c)
    (F : TwoSpeciesParticleSpace K jetOrder a c) :
    twoSpeciesPairing (twoSpeciesDeltaMode (K := K) b) F = F b := by
  simp [twoSpeciesPairing, twoSpeciesDeltaMode]

theorem twoSpeciesPairing_sum {jetOrder a c : ℕ} {I : Type*}
    (s : Finset I) (u : I → TwoSpeciesModeSpace K jetOrder a c)
    (F : TwoSpeciesParticleSpace K jetOrder a c) :
    twoSpeciesPairing (∑ i ∈ s, u i) F =
      ∑ i ∈ s, twoSpeciesPairing (u i) F := by
  classical
  simp only [twoSpeciesPairing, Finset.sum_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

/-- Ordered pairs of finite-jet modes contributing to the coefficient of total power `q` in a
product of two fields. -/
def coefficientPairs (jetOrder q : ℕ) :
    Finset (Fin (jetOrder + 1) × Fin (jetOrder + 1)) :=
  Finset.univ.filter (fun rs ↦ (rs.1 : ℕ) + (rs.2 : ℕ) = q)

@[simp]
theorem mem_coefficientPairs {jetOrder q : ℕ}
    (r s : Fin (jetOrder + 1)) :
    (r, s) ∈ coefficientPairs jetOrder q ↔ (r : ℕ) + (s : ℕ) = q := by
  simp [coefficientPairs]

/-- Forget the ordering of a finite block of mode indices.  Ordered blocks are used in field
products, while their images are commutative mode monomials. -/
def unorderedModeBlock {jetOrder arity : ℕ}
    (r : Fin arity → Fin (jetOrder + 1)) : ModeConfiguration jetOrder arity :=
  Sym.ofVector (List.Vector.ofFn r)

/-- Total derivative degree of an ordered block of field modes. -/
def orderedBlockDegree {jetOrder arity : ℕ}
    (r : Fin arity → Fin (jetOrder + 1)) : ℕ :=
  ∑ i, (r i : ℕ)

/-- Ordered `arity`-tuples contributing to the coefficient of total power `q` in a field power.
Keeping these tuples ordered is what produces the correct multinomial coefficients after passage
to the commutative mode basis. -/
def coefficientBlocks (jetOrder arity q : ℕ) :
    Finset (Fin arity → Fin (jetOrder + 1)) :=
  Finset.univ.filter (fun r ↦ orderedBlockDegree r = q)

@[simp]
theorem mem_coefficientBlocks {jetOrder arity q : ℕ}
    (r : Fin arity → Fin (jetOrder + 1)) :
    r ∈ coefficientBlocks jetOrder arity q ↔ orderedBlockDegree r = q := by
  simp [coefficientBlocks]

/-- The coefficient of `A(z)^arity` multiplying a fixed same-species spectator monomial. -/
def fieldPowerMode {jetOrder arity spectatorCount : ℕ} (q : ℕ)
    (spectator : ModeConfiguration jetOrder spectatorCount) :
    JetModeSpace K jetOrder (arity + spectatorCount) :=
  ∑ r ∈ coefficientBlocks jetOrder arity q,
    jetDeltaMode (K := K) ((unorderedModeBlock r).append spectator)

/-- Literal coincidence of `arity` new same-species particle coordinates, in coefficient form. -/
def fieldPowerDiagonalCoefficient {jetOrder arity spectatorCount : ℕ} (q : ℕ)
    (spectator : ModeConfiguration jetOrder spectatorCount)
    (F : JetParticleSpace K jetOrder (arity + spectatorCount)) : K :=
  ∑ r ∈ coefficientBlocks jetOrder arity q,
    F ((unorderedModeBlock r).append spectator)

/-- Multiplication by a coefficient of `A(z)^arity` is adjoint to literal coincidence of the
`arity` new particle coordinates.  Because `coefficientBlocks` consists of ordered tuples, this
statement includes all repeated-mode multinomial factors. -/
theorem fieldPower_adjoint_diagonal {jetOrder arity spectatorCount : ℕ} (q : ℕ)
    (spectator : ModeConfiguration jetOrder spectatorCount)
    (F : JetParticleSpace K jetOrder (arity + spectatorCount)) :
    jetModeParticlePairing (fieldPowerMode (K := K) q spectator) F =
      fieldPowerDiagonalCoefficient q spectator F := by
  rw [fieldPowerMode, jetModeParticlePairing_sum]
  simp [fieldPowerDiagonalCoefficient]

/-- Orthogonality to every coefficient of `A(z)^arity` times every spectator is exactly the
family of coincidence-diagonal vanishings. -/
theorem fieldPower_orthogonal_iff_diagonal
    {jetOrder arity spectatorCount : ℕ}
    (F : JetParticleSpace K jetOrder (arity + spectatorCount)) :
    (∀ q spectator,
        jetModeParticlePairing (fieldPowerMode (K := K) q spectator) F = 0) ↔
      ∀ q spectator, fieldPowerDiagonalCoefficient q spectator F = 0 := by
  simp only [fieldPower_adjoint_diagonal]

/-- Ordered mode data for one `A` particle and `sArity` particles of a second species, with total
derivative degree `q`. -/
def mixedCoefficientBlocks (jetOrder sArity q : ℕ) :
    Finset (Fin (jetOrder + 1) × (Fin sArity → Fin (jetOrder + 1))) :=
  Finset.univ.filter (fun r ↦ (r.1 : ℕ) + orderedBlockDegree r.2 = q)

@[simp]
theorem mem_mixedCoefficientBlocks {jetOrder sArity q : ℕ}
    (r : Fin (jetOrder + 1) × (Fin sArity → Fin (jetOrder + 1))) :
    r ∈ mixedCoefficientBlocks jetOrder sArity q ↔
      (r.1 : ℕ) + orderedBlockDegree r.2 = q := by
  simp [mixedCoefficientBlocks]

/-- The coefficient of `A(z) S(z)^sArity` multiplying fixed spectators of the two species. -/
def mixedFieldProductMode {jetOrder sArity a d : ℕ} (q : ℕ)
    (aSpectator : ModeConfiguration jetOrder a)
    (sSpectator : ModeConfiguration jetOrder d) :
    TwoSpeciesModeSpace K jetOrder (a + 1) (sArity + d) :=
  ∑ r ∈ mixedCoefficientBlocks jetOrder sArity q,
    twoSpeciesDeltaMode (K := K)
      (r.1 ::ₛ aSpectator, (unorderedModeBlock r.2).append sSpectator)

/-- Literal coincidence coefficient for one new `A` coordinate and `sArity` new `S`
coordinates. -/
def mixedDiagonalCoefficient {jetOrder sArity a d : ℕ} (q : ℕ)
    (aSpectator : ModeConfiguration jetOrder a)
    (sSpectator : ModeConfiguration jetOrder d)
    (F : TwoSpeciesParticleSpace K jetOrder (a + 1) (sArity + d)) : K :=
  ∑ r ∈ mixedCoefficientBlocks jetOrder sArity q,
    F (r.1 ::ₛ aSpectator, (unorderedModeBlock r.2).append sSpectator)

/-- Multiplication by a coefficient of `A(z) S(z)^sArity` is adjoint to coincidence of the new
`A` coordinate with the `sArity` new `S` coordinates. -/
theorem mixedFieldProduct_adjoint_diagonal {jetOrder sArity a d : ℕ} (q : ℕ)
    (aSpectator : ModeConfiguration jetOrder a)
    (sSpectator : ModeConfiguration jetOrder d)
    (F : TwoSpeciesParticleSpace K jetOrder (a + 1) (sArity + d)) :
    twoSpeciesPairing
        (mixedFieldProductMode (K := K) q aSpectator sSpectator) F =
      mixedDiagonalCoefficient q aSpectator sSpectator F := by
  rw [mixedFieldProductMode, twoSpeciesPairing_sum]
  simp [mixedDiagonalCoefficient]

/-- Orthogonality to every coefficient of `A(z) S(z)^sArity` times every spectator is exactly
the family of mixed coincidence-diagonal vanishings. -/
theorem mixedFieldProduct_orthogonal_iff_diagonal
    {jetOrder sArity a d : ℕ}
    (F : TwoSpeciesParticleSpace K jetOrder (a + 1) (sArity + d)) :
    (∀ q aSpectator sSpectator,
        twoSpeciesPairing
          (mixedFieldProductMode (K := K) q aSpectator sSpectator) F = 0) ↔
      ∀ q aSpectator sSpectator,
        mixedDiagonalCoefficient q aSpectator sSpectator F = 0 := by
  simp only [mixedFieldProduct_adjoint_diagonal]

/-- The coefficient of `X(z) Z(z)` multiplying a fixed spectator mode monomial.  The inserted
modes belong to different species, so there is one term for every ordered degree pair. -/
def xzFieldProductMode {jetOrder a c : ℕ} (q : ℕ)
    (bx : ModeConfiguration jetOrder a) (bz : ModeConfiguration jetOrder c) :
    TwoSpeciesModeSpace K jetOrder (a + 1) (c + 1) :=
  ∑ rs ∈ coefficientPairs jetOrder q,
    twoSpeciesDeltaMode (K := K) (rs.1 ::ₛ bx, rs.2 ::ₛ bz)

/-- Literal `X=Z=t` diagonal coefficient in the two newly inserted particle coordinates. -/
def xzDiagonalCoefficient {jetOrder a c : ℕ} (q : ℕ)
    (bx : ModeConfiguration jetOrder a) (bz : ModeConfiguration jetOrder c)
    (F : TwoSpeciesParticleSpace K jetOrder (a + 1) (c + 1)) : K :=
  ∑ rs ∈ coefficientPairs jetOrder q, F (rs.1 ::ₛ bx, rs.2 ::ₛ bz)

/-- Multiplication by the coefficient of `X(z) Z(z)` is adjoint to literal coincidence of the
new `X` and `Z` particle coordinates. -/
theorem xzFieldProduct_adjoint_diagonal {jetOrder a c : ℕ} (q : ℕ)
    (bx : ModeConfiguration jetOrder a) (bz : ModeConfiguration jetOrder c)
    (F : TwoSpeciesParticleSpace K jetOrder (a + 1) (c + 1)) :
    twoSpeciesPairing (xzFieldProductMode (K := K) q bx bz) F =
      xzDiagonalCoefficient q bx bz F := by
  rw [xzFieldProductMode, twoSpeciesPairing_sum]
  simp [xzDiagonalCoefficient]

/-- The coefficient of `Y(z)^2` multiplying a fixed spectator mode monomial.  The convolution is
ordered even though the resulting commutative configuration is unordered. -/
def yyFieldSquareMode {jetOrder b : ℕ} (q : ℕ)
    (byy : ModeConfiguration jetOrder b) : JetModeSpace K jetOrder (b + 2) :=
  ∑ rs ∈ coefficientPairs jetOrder q,
    jetDeltaMode (K := K) (rs.1 ::ₛ rs.2 ::ₛ byy)

/-- Literal `y_1=y_2=t` diagonal coefficient in the two newly inserted `Y` coordinates. -/
def yyDiagonalCoefficient {jetOrder b : ℕ} (q : ℕ)
    (byy : ModeConfiguration jetOrder b)
    (F : JetParticleSpace K jetOrder (b + 2)) : K :=
  ∑ rs ∈ coefficientPairs jetOrder q, F (rs.1 ::ₛ rs.2 ::ₛ byy)

/-- Multiplication by the coefficient of `Y(z)^2` is adjoint to literal coincidence of the two
new `Y` particle coordinates. -/
theorem yyFieldSquare_adjoint_diagonal {jetOrder b : ℕ} (q : ℕ)
    (byy : ModeConfiguration jetOrder b)
    (F : JetParticleSpace K jetOrder (b + 2)) :
    jetModeParticlePairing (yyFieldSquareMode (K := K) q byy) F =
      yyDiagonalCoefficient q byy F := by
  rw [yyFieldSquareMode, jetModeParticlePairing_sum]
  simp [yyDiagonalCoefficient]

section PolarizedConeRelation

/-- Three current-species mode configurations in fixed multidegree `(a,b,c)`. -/
structure CurrentConfiguration (jetOrder a b c : ℕ) where
  xModes : ModeConfiguration jetOrder a
  yModes : ModeConfiguration jetOrder b
  zModes : ModeConfiguration jetOrder c
deriving DecidableEq

private def currentConfigurationEquiv (jetOrder a b c : ℕ) :
    (ModeConfiguration jetOrder a ×
      ModeConfiguration jetOrder b × ModeConfiguration jetOrder c) ≃
      CurrentConfiguration jetOrder a b c where
  toFun d := { xModes := d.1, yModes := d.2.1, zModes := d.2.2 }
  invFun d := (d.xModes, d.yModes, d.zModes)
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance currentConfigurationFintype (jetOrder a b c : ℕ) :
    Fintype (CurrentConfiguration jetOrder a b c) :=
  Fintype.ofEquiv
    (ModeConfiguration jetOrder a ×
      ModeConfiguration jetOrder b × ModeConfiguration jetOrder c)
    (currentConfigurationEquiv jetOrder a b c)

/-- Coefficients in one fixed three-current-species finite-jet multidegree. -/
abbrev CurrentCoefficientSpace (K : Type u) (jetOrder a b c : ℕ) :=
  CurrentConfiguration jetOrder a b c → K

/-- Coordinate pairing in a three-current-species multidegree. -/
def currentPairing {jetOrder a b c : ℕ}
    (u F : CurrentCoefficientSpace K jetOrder a b c) : K :=
  ∑ d, u d * F d

/-- Delta vector at one three-current-species configuration. -/
def currentDeltaMode {jetOrder a b c : ℕ}
    (d : CurrentConfiguration jetOrder a b c) :
    CurrentCoefficientSpace K jetOrder a b c :=
  fun e ↦ if e = d then 1 else 0

@[simp]
theorem currentPairing_delta {jetOrder a b c : ℕ}
    (d : CurrentConfiguration jetOrder a b c)
    (F : CurrentCoefficientSpace K jetOrder a b c) :
    currentPairing (currentDeltaMode (K := K) d) F = F d := by
  simp [currentPairing, currentDeltaMode]

@[simp]
theorem currentPairing_neg {jetOrder a b c : ℕ}
    (u F : CurrentCoefficientSpace K jetOrder a b c) :
    currentPairing (-u) F = -currentPairing u F := by
  simp [currentPairing]

theorem currentPairing_sum {jetOrder a b c : ℕ} {I : Type*}
    (s : Finset I) (u : I → CurrentCoefficientSpace K jetOrder a b c)
    (F : CurrentCoefficientSpace K jetOrder a b c) :
    currentPairing (∑ i ∈ s, u i) F = ∑ i ∈ s, currentPairing (u i) F := by
  classical
  simp only [currentPairing, Finset.sum_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

/-- The direct sum of the two polarized current sectors coupled by `Q=XZ-Y^2`.  They have
different species multidegrees but the same total current-particle number. -/
abbrev PolarizedConeCoefficients (K : Type u) (jetOrder a b c : ℕ) :=
  CurrentCoefficientSpace K jetOrder (a + 1) b (c + 1) ×
    CurrentCoefficientSpace K jetOrder a (b + 2) c

/-- Pairing on the direct sum of the polarized `XZ` and `YY` channels. -/
def polarizedConePairing {jetOrder a b c : ℕ}
    (u F : PolarizedConeCoefficients K jetOrder a b c) : K :=
  currentPairing u.1 F.1 + currentPairing u.2 F.2

/-- The coefficient of `X(z)Z(z)-Y(z)^2` multiplying a fixed current spectator monomial.  The
minus sign is part of the relation vector, while both field products retain their ordered
convolution normalization. -/
def polarizedConeRelationMode {jetOrder a b c : ℕ} (q : ℕ)
    (bx : ModeConfiguration jetOrder a)
    (byy : ModeConfiguration jetOrder b)
    (bz : ModeConfiguration jetOrder c) :
    PolarizedConeCoefficients K jetOrder a b c :=
  (∑ rs ∈ coefficientPairs jetOrder q,
    currentDeltaMode (K := K)
      { xModes := rs.1 ::ₛ bx, yModes := byy, zModes := rs.2 ::ₛ bz },
  -∑ rs ∈ coefficientPairs jetOrder q,
    currentDeltaMode (K := K)
      { xModes := bx, yModes := rs.1 ::ₛ rs.2 ::ₛ byy, zModes := bz })

/-- Literal `XZ` collision-diagonal coefficient with all three current spectator species
retained. -/
def polarizedXZDiagonalCoefficient {jetOrder a b c : ℕ} (q : ℕ)
    (bx : ModeConfiguration jetOrder a)
    (byy : ModeConfiguration jetOrder b)
    (bz : ModeConfiguration jetOrder c)
    (F : PolarizedConeCoefficients K jetOrder a b c) : K :=
  ∑ rs ∈ coefficientPairs jetOrder q,
    F.1 { xModes := rs.1 ::ₛ bx, yModes := byy, zModes := rs.2 ::ₛ bz }

/-- Literal `YY` collision-diagonal coefficient with all three current spectator species
retained. -/
def polarizedYYDiagonalCoefficient {jetOrder a b c : ℕ} (q : ℕ)
    (bx : ModeConfiguration jetOrder a)
    (byy : ModeConfiguration jetOrder b)
    (bz : ModeConfiguration jetOrder c)
    (F : PolarizedConeCoefficients K jetOrder a b c) : K :=
  ∑ rs ∈ coefficientPairs jetOrder q,
    F.2 { xModes := bx, yModes := rs.1 ::ₛ rs.2 ::ₛ byy, zModes := bz }

/-- Exact polarized adjoint identity for `Q=XZ-Y^2`. -/
theorem polarizedConeRelation_adjoint_diagonal {jetOrder a b c : ℕ} (q : ℕ)
    (bx : ModeConfiguration jetOrder a)
    (byy : ModeConfiguration jetOrder b)
    (bz : ModeConfiguration jetOrder c)
    (F : PolarizedConeCoefficients K jetOrder a b c) :
    polarizedConePairing
        (polarizedConeRelationMode (K := K) q bx byy bz) F =
      polarizedXZDiagonalCoefficient q bx byy bz F -
        polarizedYYDiagonalCoefficient q bx byy bz F := by
  simp [polarizedConePairing, polarizedConeRelationMode,
    polarizedXZDiagonalCoefficient, polarizedYYDiagonalCoefficient,
    currentPairing_sum, sub_eq_add_neg]

/-- A polarized particle family annihilates every coefficient of `Q` times every current
spectator if and only if its `XZ` and `YY` literal diagonal restrictions agree coefficientwise. -/
theorem polarizedCone_orthogonal_iff_diagonal {jetOrder a b c : ℕ}
    (F : PolarizedConeCoefficients K jetOrder a b c) :
    (∀ q bx byy bz,
        polarizedConePairing
          (polarizedConeRelationMode (K := K) q bx byy bz) F = 0) ↔
      ∀ q bx byy bz,
        polarizedXZDiagonalCoefficient q bx byy bz F =
          polarizedYYDiagonalCoefficient q bx byy bz F := by
  simp only [polarizedConeRelation_adjoint_diagonal, sub_eq_zero]

end PolarizedConeRelation

/-- One ordered off-diagonal `Y^2` contribution pairs with the corresponding coefficient. -/
theorem yyOrderedContribution_pairing {jetOrder b : ℕ}
    (r s : Fin (jetOrder + 1)) (byy : ModeConfiguration jetOrder b)
    (F : JetParticleSpace K jetOrder (b + 2)) :
    jetModeParticlePairing
        (jetDeltaMode (K := K) (r ::ₛ s ::ₛ byy)) F =
      F (r ::ₛ s ::ₛ byy) := by
  simp

/-- Exact `Y^2` normalization off the degree diagonal: the two ordered convolution terms become
the same commutative mode monomial and therefore contribute the scalar `2`. -/
theorem yyTwoOrders_pairing {jetOrder b : ℕ}
    (r s : Fin (jetOrder + 1)) (_hrs : r ≠ s) (byy : ModeConfiguration jetOrder b)
    (F : JetParticleSpace K jetOrder (b + 2)) :
    jetModeParticlePairing
        (jetDeltaMode (K := K) (r ::ₛ s ::ₛ byy) +
          jetDeltaMode (K := K) (s ::ₛ r ::ₛ byy)) F =
      2 * F (r ::ₛ s ::ₛ byy) := by
  have hswap : s ::ₛ r ::ₛ byy = r ::ₛ s ::ₛ byy := Sym.cons_swap s r byy
  rw [hswap]
  rw [jetModeParticlePairing_add, jetModeParticlePairing_delta]
  exact (two_mul _).symm

/-- Exact `Y^2` normalization on the degree diagonal: the ordered convolution has only the one
index pair `(r,r)`, so that contribution occurs once. -/
theorem yyDiagonalOrder_pairing {jetOrder b : ℕ}
    (r : Fin (jetOrder + 1)) (byy : ModeConfiguration jetOrder b)
    (F : JetParticleSpace K jetOrder (b + 2)) :
    jetModeParticlePairing
        (jetDeltaMode (K := K) (r ::ₛ r ::ₛ byy)) F =
      F (r ::ₛ r ::ₛ byy) := by
  simp

/-- Every `XZ` field-product summand has the expected derivative degree. -/
theorem xz_insert_modeDegree {jetOrder a c : ℕ}
    (r s : Fin (jetOrder + 1))
    (bx : ModeConfiguration jetOrder a) (bz : ModeConfiguration jetOrder c) :
    modeDegree (r ::ₛ bx) + modeDegree (s ::ₛ bz) =
      modeDegree bx + modeDegree bz + ((r : ℕ) + (s : ℕ)) := by
  simp [add_assoc, add_left_comm, add_comm]

/-- Every `Y^2` field-product summand has the expected derivative degree. -/
theorem yy_insert_modeDegree {jetOrder b : ℕ}
    (r s : Fin (jetOrder + 1)) (byy : ModeConfiguration jetOrder b) :
    modeDegree (r ::ₛ s ::ₛ byy) =
      modeDegree byy + ((r : ℕ) + (s : ℕ)) := by
  simp [add_assoc, add_comm]

end FullFiniteJetPairing

end

end VOA.ModeParticlePairing
