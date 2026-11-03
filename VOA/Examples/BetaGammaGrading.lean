/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Examples.BetaGamma
import Mathlib.Algebra.MvPolynomial.Derivation
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# `βγ`: the **half-integer** conformal weight grading

This is the first grading in the library that genuinely needs the `ℂ`-valued index of
`SuperVertexAlgebra.grading`: the generating states sit at conformal weight `1/2`, and
`gradingBG_notMem_intCast_witness` proves outright that a nonzero weight space sits at a weight
which is **not** the image of any integer.  The other constructed gradings (Heisenberg,
lattice, symplectic fermions) take values in `ℕ ⊆ ℤ ⊆ ℂ` and can be relabelled by `ℤ`.

## The weight assignment, and how it is derived

`Examples/BetaGamma` gives `beta gamma : FormalDist (Module.End ℂ Fock)` with

  `beta n = der (inr n.toNat)` for `n ≥ 0`,  `beta n = mulX (inl (-n-1).toNat)` for `n < 0`,

and the canonical commutation relation `beta m * gamma n - gamma n * beta m = δ_{m+n+1,0}`.

**Which index convention is `n`?**  The repository writes a field as `a(z) = ∑ⱼ a j zʲ` and
recovers its vertex-algebra modes by `mode a n = a (-n-1)` (`Foundations.FormalCalculus`), and
`Core.Dong.IsField` asks for *lower* truncation `a j x = 0` for `j ≪ 0`.  Now `beta j` for
`j ≪ 0` is multiplication by `X (inl (-j-1))`, which never vanishes, while `beta j` for `j ≫ 0`
is `∂/∂(X (inr j))`, which *does* vanish on any fixed polynomial.  So `beta` is **upper**
truncated in its own index: it is not the `zʲ`-coefficient family, it is the family of
**vertex-algebra modes** `beta n = β₍ₙ₎`, and the associated field is `fun j => beta (-j-1)`.
(That is also the only reading compatible with the vacuum axiom: `β₍ₙ₎1 = 0` for `n ≥ 0`
holds, since `der i 1 = 0`.)

With that fixed, the weight assignment is forced.  In a graded vertex algebra
`a₍ₙ₎ : V_c → V_{c + hₐ - n - 1}`, so `β₍ₙ₎` shifts the weight by `-n - 1 + h_β`.  The
commutation relation `[β₍ₘ₎, γ₍ₙ₎] = δ_{m+n+1,0}·id` forces the two shifts to cancel exactly when
`m + n + 1 = 0`, i.e. `(-m - 1 + h_β) + (-n - 1 + h_γ) = 0` whenever `m + n + 1 = 0`, i.e.
`h_β + h_γ = 1`; and the construction is symmetric under `β ↔ γ` (`inl ↔ inr`), so
`h_β = h_γ = 1/2`.  This is the `λ = 1/2` symplectic-boson point.  Consequently

  `X (inl k) = β₍₋ₖ₋₁₎ 1` has weight `-(-k-1) - 1 + 1/2 = k + 1/2`,
  `X (inr k) = γ₍₋ₖ₋₁₎ 1` has weight `k + 1/2`,

which is `bgWt` below (`bgWt_inl`, `bgWt_inr`; the identifications `X (inl k) = β₍₋ₖ₋₁₎1` and
`X (inr k) = γ₍₋ₖ₋₁₎1` are `X_inl_eq_beta_vacuum`, `X_inr_eq_gamma_vacuum`).  The derivation is
*checked*, not assumed: `beta_mem_gradingBG` / `gamma_mem_gradingBG` prove that with this
assignment `β₍ₙ₎` and `γ₍ₙ₎` really do map `V_c` into `V_{c - n - 1/2}`, which is the
graded-vertex-algebra law `a₍ₙ₎ : V_c → V_{c + hₐ - n - 1}` at `hₐ = 1/2`.

Nothing about the central charge is claimed here; for the record the standard `βγ` system at
`λ = 1/2` has `c = -1`, but that belongs to a Virasoro file, not to this one.

## Construction

The Fock space is the *polynomial* algebra `MvPolynomial (ℕ ⊕ ℕ) ℂ`, so the weight operator is
the Euler-type derivation `L₀ = ∑ᵢ wᵢ Xᵢ ∂ᵢ`, built in one line with
`MvPolynomial.mkDerivation` (no dual-number device is needed, unlike the Clifford-algebra
construction in `Examples/SymplecticFermionGrading`).  Its eigenvalue on a monomial is the
`Finsupp.weight bgWt` of the exponent vector (`L0BG_monomial`).

The graded pieces are the weighted-homogeneous submodules for the `ℂ`-valued weight `bgWt`.
Independence is then **free**, exactly as in the symplectic-fermion file: the pieces are
contained in the eigenspaces of the *single* operator `L₀`, and distinct eigenspaces of one
endomorphism are automatically independent (`Module.End.eigenspaces_iSupIndep`).  Indexing the
grading by `ℂ` makes "eigenvalue" and "grading index" literally the same variable.

Finite-dimensionality uses that every generator contributes at least `1/2`: doubling the weight
gives the `ℕ`-valued weight `bgWt2 i = 2·level i + 1`, and only finitely many exponent vectors
have a given `bgWt2`.
-/

namespace VOA.BGGrad

open MvPolynomial

/-- The `βγ` Fock space `ℂ[X_{inl k}, X_{inr k}]`, re-exported from `Examples.BetaGamma`. -/
noncomputable abbrev FockBG : Type := VOA.BetaGamma.Fock

/-! ## §1  The weight of a generator -/

/-- The **level** of a generator index: `X (inl k)` and `X (inr k)` both sit at level `k`.
(`inl` is created by `β`, `inr` by `γ`.) -/
def bgLevel : ℕ ⊕ ℕ → ℕ := Sum.elim id id

@[simp] theorem bgLevel_inl (k : ℕ) : bgLevel (Sum.inl k) = k := rfl

@[simp] theorem bgLevel_inr (k : ℕ) : bgLevel (Sum.inr k) = k := rfl

/-- **The conformal weight of a generator**: `X (inl k) = β₍₋ₖ₋₁₎1` and
`X (inr k) = γ₍₋ₖ₋₁₎1` both have weight `k + 1/2`.  This is the half-integer that the whole
file exists to exhibit. -/
noncomputable def bgWt : (ℕ ⊕ ℕ) → ℂ := fun i => (bgLevel i : ℂ) + 1 / 2

@[simp] theorem bgWt_inl (k : ℕ) : bgWt (Sum.inl k) = (k : ℂ) + 1 / 2 := by
  simp [bgWt]

@[simp] theorem bgWt_inr (k : ℕ) : bgWt (Sum.inr k) = (k : ℂ) + 1 / 2 := by
  simp [bgWt]

/-- **The lowest generator sits at weight `1/2`.** -/
theorem bgWt_inl_zero : bgWt (Sum.inl 0) = 1 / 2 := by simp

/-- Twice the weight, as a **natural number**: `2·level + 1`, always odd and always `≥ 1`.
This is the bookkeeping device that makes the finiteness arguments elementary. -/
def bgWt2 : (ℕ ⊕ ℕ) → ℕ := fun i => 2 * bgLevel i + 1

theorem bgWt2_pos (i : ℕ ⊕ ℕ) : 0 < bgWt2 i := by
  simp [bgWt2]

theorem bgWt2_ne_zero (i : ℕ ⊕ ℕ) : bgWt2 i ≠ 0 := by
  simp [bgWt2]

theorem bgWt2_cast (i : ℕ ⊕ ℕ) : ((bgWt2 i : ℕ) : ℂ) = 2 * bgWt i := by
  simp only [bgWt2, bgWt, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  ring

/-- The complex weight and the doubled natural weight of an exponent vector agree, up to the
factor `2`.  Everything about "the weights are half-integers" comes from this line. -/
theorem weight_bgWt2_cast (d : (ℕ ⊕ ℕ) →₀ ℕ) :
    ((Finsupp.weight bgWt2 d : ℕ) : ℂ) = 2 * Finsupp.weight bgWt d := by
  classical
  rw [Finsupp.weight_apply, Finsupp.weight_apply, Finsupp.sum, Finsupp.sum, Nat.cast_sum,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_eq_mul, Nat.cast_mul, bgWt2_cast, nsmul_eq_mul]
  ring

/-! ## §2  The weight operator `L₀` -/

/-- **The weight operator as a derivation**: `L₀ = ∑ᵢ wᵢ Xᵢ ∂ᵢ`, the Euler-type derivation of
the polynomial algebra determined by `L₀(Xᵢ) = wᵢ Xᵢ`.  On a polynomial algebra this replaces
the dual-number construction that `Examples/SymplecticFermionGrading` needs for a Clifford
algebra. -/
noncomputable def L0BGder : Derivation ℂ FockBG FockBG :=
  MvPolynomial.mkDerivation ℂ fun i => bgWt i • (X i : FockBG)

/-- **The weight operator `L₀`** on the `βγ` Fock space. -/
noncomputable def L0BG : Module.End ℂ FockBG := L0BGder.toLinearMap

@[simp] theorem L0BG_apply (p : FockBG) : L0BG p = L0BGder p := rfl

@[simp] theorem L0BG_X (i : ℕ ⊕ ℕ) : L0BG (X i) = bgWt i • (X i : FockBG) := by
  rw [L0BG_apply, L0BGder, MvPolynomial.mkDerivation_X]

@[simp] theorem L0BG_C (a : ℂ) : L0BG (C a : FockBG) = 0 := by
  rw [L0BG_apply]
  exact MvPolynomial.derivation_C L0BGder a

@[simp] theorem L0BG_one : L0BG (1 : FockBG) = 0 := by
  rw [L0BG_apply]
  exact L0BGder.map_one_eq_zero

/-- **`L₀` is a derivation** — this *is* the statement that conformal weights add when states
are multiplied. -/
theorem L0BG_mul (p q : FockBG) : L0BG (p * q) = p * L0BG q + q * L0BG p := by
  rw [L0BG_apply, L0BG_apply, L0BG_apply, L0BGder.leibniz, smul_eq_mul, smul_eq_mul]

/-- `L₀` on a pure power: `Xᵢⁿ` has weight `n·wᵢ`. -/
theorem L0BG_X_pow (i : ℕ ⊕ ℕ) (n : ℕ) :
    L0BG ((X i : FockBG) ^ n) = ((n : ℂ) * bgWt i) • (X i : FockBG) ^ n := by
  induction n with
  | zero => simp
  | succ m ih =>
      rw [pow_succ, L0BG_mul, ih, L0BG_X]
      simp only [MvPolynomial.smul_eq_C_mul, map_add, map_mul, map_one, Nat.cast_succ]
      ring

/-- **Every monomial is an `L₀`-eigenvector**, with eigenvalue the weighted degree of its
exponent vector.  This one computation carries the whole grading. -/
theorem L0BG_monomial (d : (ℕ ⊕ ℕ) →₀ ℕ) (a : ℂ) :
    L0BG (monomial d a) = (Finsupp.weight bgWt d) • (monomial d a : FockBG) := by
  classical
  induction d using Finsupp.induction with
  | zero =>
      have h0 : Finsupp.weight bgWt (0 : (ℕ ⊕ ℕ) →₀ ℕ) = 0 := map_zero _
      rw [h0, zero_smul, ← MvPolynomial.C_apply]
      exact L0BG_C a
  | single_add i n d' _ _ ih =>
      have hsplit : (monomial (Finsupp.single i n + d') a : FockBG)
          = (X i : FockBG) ^ n * monomial d' a := by
        rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_mul, one_mul]
      rw [hsplit, L0BG_mul, ih, L0BG_X_pow, map_add, Finsupp.weight_single]
      simp only [MvPolynomial.smul_eq_C_mul, map_add, map_mul, nsmul_eq_mul]
      ring

/-! ## §3  The grading -/

/-- **The conformal weight grading of the `βγ` Fock space**, indexed by `ℂ`: the weight-`c`
piece is the span of the monomials of weighted degree `c`, for the **half-integer** weight
`bgWt`. -/
noncomputable def gradingBG (c : ℂ) : Submodule ℂ FockBG :=
  MvPolynomial.weightedHomogeneousSubmodule ℂ bgWt c

theorem mem_gradingBG {c : ℂ} {p : FockBG} :
    p ∈ gradingBG c ↔ p.IsWeightedHomogeneous bgWt c :=
  MvPolynomial.mem_weightedHomogeneousSubmodule ℂ bgWt c p

theorem monomial_mem_gradingBG (d : (ℕ ⊕ ℕ) →₀ ℕ) (a : ℂ) :
    (monomial d a : FockBG) ∈ gradingBG (Finsupp.weight bgWt d) :=
  mem_gradingBG.mpr (MvPolynomial.isWeightedHomogeneous_monomial _ _ _ rfl)

/-- The vacuum `1` has weight `0`. -/
theorem one_mem_gradingBG : (1 : FockBG) ∈ gradingBG 0 :=
  mem_gradingBG.mpr (MvPolynomial.isWeightedHomogeneous_one ℂ bgWt)

/-- `X i` sits in the weight space of its own weight — for `i = inl 0` this is weight
`1/2`. -/
theorem X_mem_gradingBG (i : ℕ ⊕ ℕ) : (X i : FockBG) ∈ gradingBG (bgWt i) :=
  mem_gradingBG.mpr (MvPolynomial.isWeightedHomogeneous_X ℂ bgWt i)

/-- Every homogeneous element is an `L₀`-eigenvector: expand it over its monomials, all of
which have the same weighted degree. -/
theorem L0BG_eq_smul_of_mem {c : ℂ} {p : FockBG} (hp : p ∈ gradingBG c) : L0BG p = c • p := by
  classical
  have hh : p.IsWeightedHomogeneous bgWt c := mem_gradingBG.mp hp
  conv_lhs => rw [MvPolynomial.as_sum p]
  conv_rhs => rw [MvPolynomial.as_sum p]
  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdw : Finsupp.weight bgWt d = c := hh (MvPolynomial.mem_support_iff.mp hd)
  rw [L0BG_monomial, hdw]

/-- Each graded piece sits inside the corresponding `L₀`-eigenspace. -/
theorem gradingBG_le_eigenspace (c : ℂ) : gradingBG c ≤ Module.End.eigenspace L0BG c := by
  intro p hp
  rw [Module.End.mem_eigenspace_iff]
  exact L0BG_eq_smul_of_mem hp

/-- **The graded pieces are independent**, for free: they lie inside the eigenspaces of the
*single* operator `L₀`, and distinct eigenspaces of one endomorphism always meet in `0`
(`Module.End.eigenspaces_iSupIndep`).  Because the grading is indexed by `ℂ`, "eigenvalue" and
"grading index" are literally the same variable — no basis, no counting. -/
theorem gradingBG_iSupIndep : iSupIndep gradingBG :=
  (Module.End.eigenspaces_iSupIndep L0BG).mono gradingBG_le_eigenspace

/-- The graded pieces span: every polynomial is a sum of monomials, and each monomial is
homogeneous. -/
theorem gradingBG_iSup_eq_top : ⨆ c : ℂ, gradingBG c = ⊤ := by
  refine eq_top_iff.mpr fun p _ => ?_
  refine MvPolynomial.induction_on' p ?_ ?_
  · intro d a
    exact le_iSup gradingBG (Finsupp.weight bgWt d) (monomial_mem_gradingBG d a)
  · intro q r hq hr
    exact Submodule.add_mem _ hq hr

/-- **The `βγ` Fock space is the internal direct sum of its conformal weight spaces.** -/
theorem gradingBG_isInternal : DirectSum.IsInternal gradingBG :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    gradingBG_iSupIndep gradingBG_iSup_eq_top

/-- **A spanning family inside an independent family is that family** (pure lattice theory; the
modular law for submodules).  Used only to upgrade `gradingBG_le_eigenspace` to an equality. -/
theorem submodule_eq_of_le_of_iSupIndep {M : Type*} [AddCommGroup M] [Module ℂ M] {ι : Type*}
    {p q : ι → Submodule ℂ M} (hpq : ∀ i, p i ≤ q i) (hq : iSupIndep q)
    (hp : ⨆ i, p i = ⊤) (i : ι) : p i = q i := by
  have hsplit : ⨆ j, p j = p i ⊔ ⨆ (j) (_ : j ≠ i), p j := by
    refine le_antisymm (iSup_le fun j => ?_)
      (sup_le (le_iSup p i) (iSup₂_le fun j _ => le_iSup p j))
    by_cases hj : j = i
    · subst hj; exact le_sup_left
    · exact le_sup_of_le_right (le_iSup₂ (f := fun (j : ι) (_ : j ≠ i) => p j) j hj)
  have hbot : (⨆ (j) (_ : j ≠ i), p j) ⊓ q i = ⊥ := by
    rw [inf_comm]
    exact le_bot_iff.mp
      (le_trans (inf_le_inf_left (q i) (iSup₂_mono fun j _ => hpq j)) (hq i).le_bot)
  have hmod := sup_inf_assoc_of_le (α := Submodule ℂ M) (x := p i)
    (⨆ (j) (_ : j ≠ i), p j) (hpq i)
  rw [← hsplit, hp, top_inf_eq] at hmod
  rw [hmod, hbot, sup_bot_eq]

/-- `L₀` really is *the* grading operator: the weight spaces are exactly its eigenspaces. -/
theorem gradingBG_eq_eigenspace (c : ℂ) : gradingBG c = Module.End.eigenspace L0BG c :=
  submodule_eq_of_le_of_iSupIndep gradingBG_le_eigenspace
    (Module.End.eigenspaces_iSupIndep L0BG) gradingBG_iSup_eq_top c

/-! ## §4  The weights are genuinely half-integral -/

/-- `X (inl 0) = β₍₋₁₎1` is a nonzero polynomial. -/
theorem X_inl_zero_ne_zero : (X (Sum.inl 0) : FockBG) ≠ 0 :=
  MvPolynomial.X_ne_zero _

/-- **A nonzero state of conformal weight `1/2`.** -/
theorem X_inl_zero_mem_half : (X (Sum.inl 0) : FockBG) ∈ gradingBG (1 / 2) := by
  have h := X_mem_gradingBG (Sum.inl 0)
  rwa [bgWt_inl_zero] at h

/-- The weight-`1/2` space is nonzero. -/
theorem gradingBG_half_ne_bot : gradingBG (1 / 2 : ℂ) ≠ ⊥ := by
  intro h
  have hmem : (X (Sum.inl 0) : FockBG) ∈ (⊥ : Submodule ℂ FockBG) := h ▸ X_inl_zero_mem_half
  exact X_inl_zero_ne_zero ((Submodule.mem_bot ℂ).mp hmem)

/-- `1/2` is not an integer. -/
theorem half_ne_intCast (n : ℤ) : (n : ℂ) ≠ 1 / 2 := by
  intro h
  have h2 : ((2 * n : ℤ) : ℂ) = ((1 : ℤ) : ℂ) := by
    push_cast
    rw [h]; ring
  have : (2 : ℤ) * n = 1 := Int.cast_injective h2
  omega

/-- **THE POINT OF THE WHOLE TRACK.**  The `βγ` conformal weight grading has a *nonzero*
weight space at a weight that is **not** the image of any integer.  Hence this `ℂ`-indexed
grading is not a relabelled `ℤ`-grading: the `ℂ`-valued index of `SuperVertexAlgebra.grading`
is genuinely exercised here for the first time.  The witness is `β₍₋₁₎1 = X (inl 0)` at weight
`1/2`. -/
theorem gradingBG_notMem_intCast_witness :
    ∃ c : ℂ, gradingBG c ≠ ⊥ ∧ ∀ n : ℤ, (n : ℂ) ≠ c :=
  ⟨1 / 2, gradingBG_half_ne_bot, half_ne_intCast⟩

/-- Restated with `Set.range`: some occupied weight lies outside the image of `ℤ` in `ℂ`. -/
theorem exists_occupied_weight_notMem_range_intCast :
    ∃ c : ℂ, gradingBG c ≠ ⊥ ∧ c ∉ Set.range ((↑) : ℤ → ℂ) := by
  refine ⟨1 / 2, gradingBG_half_ne_bot, ?_⟩
  rintro ⟨n, hn⟩
  exact half_ne_intCast n hn

/-- Conversely the weights are *half*-integers and nothing worse: an occupied weight `c`
satisfies `2c ∈ ℕ`. -/
theorem exists_nat_two_mul_of_gradingBG_ne_bot {c : ℂ} (h : gradingBG c ≠ ⊥) :
    ∃ n : ℕ, (n : ℂ) = 2 * c := by
  classical
  obtain ⟨p, hp, hp0⟩ := Submodule.ne_bot_iff _ |>.mp h
  have hh : p.IsWeightedHomogeneous bgWt c := mem_gradingBG.mp hp
  have hne : p.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hs
    exact hp0 (MvPolynomial.support_eq_empty.mp hs)
  obtain ⟨d, hd⟩ := hne
  have hdw : Finsupp.weight bgWt d = c := hh (MvPolynomial.mem_support_iff.mp hd)
  refine ⟨Finsupp.weight bgWt2 d, ?_⟩
  rw [weight_bgWt2_cast, hdw]

/-- Contrapositive: a weight that is not a half-natural-number carries nothing. -/
theorem gradingBG_eq_bot_of_not_two_mul_nat {c : ℂ} (h : ∀ n : ℕ, (n : ℂ) ≠ 2 * c) :
    gradingBG c = ⊥ := by
  by_contra hc
  obtain ⟨n, hn⟩ := exists_nat_two_mul_of_gradingBG_ne_bot hc
  exact h n hn

/-- Not just one exceptional weight: **every** `k + 1/2` is occupied, so the set of occupied
weights meets the complement of `ℤ` in an infinite set. -/
theorem gradingBG_half_succ_ne_bot (k : ℕ) : gradingBG ((k : ℂ) + 1 / 2) ≠ ⊥ := by
  intro h
  have hmem : (X (Sum.inl k) : FockBG) ∈ (⊥ : Submodule ℂ FockBG) := by
    have hx := X_mem_gradingBG (Sum.inl k)
    rw [bgWt_inl, h] at hx
    exact hx
  exact MvPolynomial.X_ne_zero _ ((Submodule.mem_bot ℂ).mp hmem)

/-- An exponent vector of total weight `0` is the empty one: every generator has strictly
positive weight. -/
theorem eq_zero_of_weight_bgWt_eq_zero {d : (ℕ ⊕ ℕ) →₀ ℕ} (hd : Finsupp.weight bgWt d = 0) :
    d = 0 := by
  have h2 : ((Finsupp.weight bgWt2 d : ℕ) : ℂ) = ((0 : ℕ) : ℂ) := by
    rw [weight_bgWt2_cast, hd, Nat.cast_zero, mul_zero]
  have h0 : Finsupp.weight bgWt2 d = 0 := Nat.cast_injective h2
  refine Finsupp.ext fun i => ?_
  by_contra hne
  have hle : bgWt2 i ≤ Finsupp.weight bgWt2 d := Finsupp.le_weight_of_ne_zero' bgWt2 hne
  rw [h0] at hle
  exact (bgWt2_ne_zero i) (Nat.le_zero.mp hle)

/-- **The weight-`0` space is exactly the vacuum line** `ℂ·1` — the `vacuum_grade` axiom of a
conformal vertex algebra, and the statement that the grading is bounded below by `0` with a
one-dimensional bottom. -/
theorem gradingBG_zero : gradingBG 0 = (ℂ ∙ (1 : FockBG)) := by
  classical
  refine le_antisymm (fun p hp => ?_) ?_
  · have hh : p.IsWeightedHomogeneous bgWt 0 := mem_gradingBG.mp hp
    have hsupp : ∀ d ∈ p.support, d = 0 := fun d hd =>
      eq_zero_of_weight_bgWt_eq_zero (hh (MvPolynomial.mem_support_iff.mp hd))
    have hpc : p = MvPolynomial.C (MvPolynomial.coeff 0 p) := by
      refine MvPolynomial.ext _ _ fun d => ?_
      by_cases hd0 : d = 0
      · subst hd0; simp
      · have hnotmem : d ∉ p.support := fun hd => hd0 (hsupp d hd)
        rw [MvPolynomial.notMem_support_iff.mp hnotmem, MvPolynomial.coeff_C,
          if_neg (Ne.symm hd0)]
    rw [hpc, MvPolynomial.C_eq_smul_one]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact one_mem_gradingBG

/-! ## §5  The `βγ` modes are graded — the check that `h_β = h_γ = 1/2`

`a₍ₙ₎ : V_c → V_{c + hₐ - n - 1}`, so at `hₐ = 1/2` every mode of `β` and of `γ` must shift the
weight by `-n - 1/2`.  Both statements below are proved from the definitions in
`Examples.BetaGamma`, so the weight assignment of §1 is *verified*, not postulated. -/

theorem beta_apply_of_nonneg {n : ℤ} (hn : 0 ≤ n) (p : FockBG) :
    VOA.BetaGamma.beta n p = pderiv (Sum.inr n.toNat) p := by
  simp only [VOA.BetaGamma.beta, if_pos hn, VOA.BetaGamma.der_apply]

theorem beta_apply_of_neg {n : ℤ} (hn : n < 0) (p : FockBG) :
    VOA.BetaGamma.beta n p = (X (Sum.inl (-n - 1).toNat) : FockBG) * p := by
  simp only [VOA.BetaGamma.beta, if_neg (by omega : ¬ (0 : ℤ) ≤ n),
    VOA.BetaGamma.mulX_apply]

theorem gamma_apply_of_nonneg {n : ℤ} (hn : 0 ≤ n) (p : FockBG) :
    VOA.BetaGamma.gamma n p = -pderiv (Sum.inl n.toNat) p := by
  simp only [VOA.BetaGamma.gamma, if_pos hn, LinearMap.neg_apply,
    VOA.BetaGamma.der_apply]

theorem gamma_apply_of_neg {n : ℤ} (hn : n < 0) (p : FockBG) :
    VOA.BetaGamma.gamma n p = (X (Sum.inr (-n - 1).toNat) : FockBG) * p := by
  simp only [VOA.BetaGamma.gamma, if_neg (by omega : ¬ (0 : ℤ) ≤ n),
    VOA.BetaGamma.mulX_apply]

/-- `X (inl k)` is the state `β₍₋ₖ₋₁₎1`. -/
theorem X_inl_eq_beta_vacuum (k : ℕ) :
    VOA.BetaGamma.beta (-(k : ℤ) - 1) (1 : FockBG) = (X (Sum.inl k) : FockBG) := by
  rw [beta_apply_of_neg (by omega), mul_one]
  congr 2
  omega

/-- `X (inr k)` is the state `γ₍₋ₖ₋₁₎1`. -/
theorem X_inr_eq_gamma_vacuum (k : ℕ) :
    VOA.BetaGamma.gamma (-(k : ℤ) - 1) (1 : FockBG) = (X (Sum.inr k) : FockBG) := by
  rw [gamma_apply_of_neg (by omega), mul_one]
  congr 2
  omega

/-- **`β₍ₙ₎ : V_c → V_{c - n - 1/2}`** — the graded-vertex-algebra law
`a₍ₙ₎ : V_c → V_{c + hₐ - n - 1}` at `h_β = 1/2`. -/
theorem beta_mem_gradingBG {c : ℂ} {p : FockBG} (hp : p ∈ gradingBG c) (n : ℤ) :
    VOA.BetaGamma.beta n p ∈ gradingBG (c - n - 1 / 2) := by
  rcases le_or_gt 0 n with hn | hn
  · have hcast : ((n.toNat : ℕ) : ℂ) = (n : ℂ) := by exact_mod_cast Int.toNat_of_nonneg hn
    rw [beta_apply_of_nonneg hn]
    refine mem_gradingBG.mpr (MvPolynomial.IsWeightedHomogeneous.pderiv
      (mem_gradingBG.mp hp) ?_)
    rw [bgWt_inr, hcast]
    ring
  · have hcast : (((-n - 1).toNat : ℕ) : ℂ) = -(n : ℂ) - 1 := by
      have h1 : (((-n - 1).toNat : ℕ) : ℤ) = -n - 1 := Int.toNat_of_nonneg (by omega)
      exact_mod_cast h1
    rw [beta_apply_of_neg hn]
    have hmul := (MvPolynomial.isWeightedHomogeneous_X ℂ bgWt
      (Sum.inl (-n - 1).toNat)).mul (mem_gradingBG.mp hp)
    have hw : bgWt (Sum.inl (-n - 1).toNat) + c = c - n - 1 / 2 := by
      rw [bgWt_inl, hcast]; ring
    rw [hw] at hmul
    exact mem_gradingBG.mpr hmul

/-- **`γ₍ₙ₎ : V_c → V_{c - n - 1/2}`** — same law, `h_γ = 1/2`. -/
theorem gamma_mem_gradingBG {c : ℂ} {p : FockBG} (hp : p ∈ gradingBG c) (n : ℤ) :
    VOA.BetaGamma.gamma n p ∈ gradingBG (c - n - 1 / 2) := by
  rcases le_or_gt 0 n with hn | hn
  · have hcast : ((n.toNat : ℕ) : ℂ) = (n : ℂ) := by exact_mod_cast Int.toNat_of_nonneg hn
    rw [gamma_apply_of_nonneg hn]
    refine Submodule.neg_mem _ (mem_gradingBG.mpr (MvPolynomial.IsWeightedHomogeneous.pderiv
      (mem_gradingBG.mp hp) ?_))
    rw [bgWt_inl, hcast]
    ring
  · have hcast : (((-n - 1).toNat : ℕ) : ℂ) = -(n : ℂ) - 1 := by
      have h1 : (((-n - 1).toNat : ℕ) : ℤ) = -n - 1 := Int.toNat_of_nonneg (by omega)
      exact_mod_cast h1
    rw [gamma_apply_of_neg hn]
    have hmul := (MvPolynomial.isWeightedHomogeneous_X ℂ bgWt
      (Sum.inr (-n - 1).toNat)).mul (mem_gradingBG.mp hp)
    have hw : bgWt (Sum.inr (-n - 1).toNat) + c = c - n - 1 / 2 := by
      rw [bgWt_inr, hcast]; ring
    rw [hw] at hmul
    exact mem_gradingBG.mpr hmul

/-! ## §6  finrank — every weight space is finite dimensional

Each generator contributes at least `1/2`, i.e. at least `1` to the doubled weight `bgWt2`.
So a doubled weight `n` bounds every exponent by `n` and every level by `n`, leaving finitely
many exponent vectors. -/

/-- The exponent vectors of doubled weight `n`. -/
def bgDegSet (n : ℕ) : Set ((ℕ ⊕ ℕ) →₀ ℕ) := {d | Finsupp.weight bgWt2 d = n}

theorem bgDegSet_entry_le {n : ℕ} {d : (ℕ ⊕ ℕ) →₀ ℕ} (hd : d ∈ bgDegSet n) (i : ℕ ⊕ ℕ) :
    d i ≤ n := by
  have hle : d i ≤ Finsupp.weight bgWt2 d :=
    Finsupp.le_weight bgWt2 (bgWt2_ne_zero i) d
  rw [show Finsupp.weight bgWt2 d = n from hd] at hle
  exact hle

theorem bgDegSet_level_lt {n : ℕ} {d : (ℕ ⊕ ℕ) →₀ ℕ} (hd : d ∈ bgDegSet n) {i : ℕ ⊕ ℕ}
    (hi : d i ≠ 0) : bgLevel i < n := by
  have hle : bgWt2 i ≤ Finsupp.weight bgWt2 d := Finsupp.le_weight_of_ne_zero' bgWt2 hi
  rw [show Finsupp.weight bgWt2 d = n from hd] at hle
  simp only [bgWt2] at hle
  omega

/-- **Only finitely many exponent vectors have a given doubled weight.**  They are supported on
levels `< n` (two families, so the alphabet is `Fin n ⊕ Fin n`) with all exponents `≤ n`. -/
theorem bgDegSet_finite (n : ℕ) : (bgDegSet n).Finite := by
  classical
  rw [← Set.finite_coe_iff]
  refine Finite.of_injective (β := (Fin n ⊕ Fin n) → Fin (n + 1))
    (fun d j => ⟨d.1 (Sum.map Fin.val Fin.val j), by
      have := bgDegSet_entry_le d.2 (Sum.map Fin.val Fin.val j); omega⟩) ?_
  rintro ⟨d, hd⟩ ⟨e, he⟩ h
  refine Subtype.ext (Finsupp.ext fun i => ?_)
  by_cases hlt : bgLevel i < n
  · obtain ⟨j, rfl⟩ : ∃ j : Fin n ⊕ Fin n, Sum.map Fin.val Fin.val j = i := by
      cases i with
      | inl k => exact ⟨Sum.inl ⟨k, by simpa using hlt⟩, rfl⟩
      | inr k => exact ⟨Sum.inr ⟨k, by simpa using hlt⟩, rfl⟩
    have hj := congrFun h j
    simpa using congrArg Fin.val hj
  · have hdz : d i = 0 := by
      by_contra hne; exact hlt (bgDegSet_level_lt hd hne)
    have hez : e i = 0 := by
      by_contra hne; exact hlt (bgDegSet_level_lt he hne)
    rw [hdz, hez]

/-- The exponent vectors of complex weight `c`. -/
def bgDegSetC (c : ℂ) : Set ((ℕ ⊕ ℕ) →₀ ℕ) := {d | Finsupp.weight bgWt d = c}

/-- **Only finitely many monomials have a given complex conformal weight.**  If `2c` is not a
natural number there are none at all; otherwise they are the doubled-weight-`2c` exponent
vectors. -/
theorem bgDegSetC_finite (c : ℂ) : (bgDegSetC c).Finite := by
  by_cases hc : ∃ n : ℕ, (n : ℂ) = 2 * c
  · obtain ⟨n, hn⟩ := hc
    refine (bgDegSet_finite n).subset fun d hd => ?_
    have hdw : Finsupp.weight bgWt d = c := hd
    have h2 : ((Finsupp.weight bgWt2 d : ℕ) : ℂ) = ((n : ℕ) : ℂ) := by
      rw [weight_bgWt2_cast, hdw, hn]
    exact Nat.cast_injective h2
  · refine Set.Finite.subset Set.finite_empty fun d hd => ?_
    have hdw : Finsupp.weight bgWt d = c := hd
    exact absurd ⟨Finsupp.weight bgWt2 d, by rw [weight_bgWt2_cast, hdw]⟩ hc

/-- The (finite) set of weight-`c` monomials. -/
noncomputable def bgMonSet (c : ℂ) : Set FockBG :=
  (fun d => (monomial d 1 : FockBG)) '' bgDegSetC c

theorem bgMonSet_finite (c : ℂ) : (bgMonSet c).Finite := (bgDegSetC_finite c).image _

theorem gradingBG_le_span (c : ℂ) : gradingBG c ≤ Submodule.span ℂ (bgMonSet c) := by
  classical
  intro p hp
  have hh : p.IsWeightedHomogeneous bgWt c := mem_gradingBG.mp hp
  rw [MvPolynomial.as_sum p]
  refine Submodule.sum_mem _ fun d hd => ?_
  have hdw : Finsupp.weight bgWt d = c := hh (MvPolynomial.mem_support_iff.mp hd)
  have hmem : (monomial d 1 : FockBG) ∈ bgMonSet c := ⟨d, hdw, rfl⟩
  have hscale : (monomial d (MvPolynomial.coeff d p) : FockBG)
      = (MvPolynomial.coeff d p) • monomial d 1 := by
    rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  rw [hscale]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

/-- **Every conformal weight space is finite dimensional.** -/
theorem gradingBG_finiteDimensional (c : ℂ) : FiniteDimensional ℂ (gradingBG c) := by
  have hspan : FiniteDimensional ℂ (Submodule.span ℂ (bgMonSet c)) :=
    FiniteDimensional.span_of_finite ℂ (bgMonSet_finite c)
  exact Submodule.finiteDimensional_of_le (gradingBG_le_span c)

instance instFiniteDimensionalGradingBG (c : ℂ) : FiniteDimensional ℂ (gradingBG c) :=
  gradingBG_finiteDimensional c

end VOA.BGGrad

