/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Examples.BetaGammaField
import VOA.Examples.BetaGammaGrading
import VOA.Core.SuperCovariant
import VOA.Core.SuperVertexAlgebra
import VOA.Core.SuperNearVOA
import VOA.Examples.BetaGammaVirasoro

/-!
# The `βγ` **super vertex algebra** — the first instance with half-integer weights

`bgSVA : SuperVertexAlgebra Fock`, assembled from the `βγ` symplectic bosons.  Every previous
`SuperVertexAlgebra`-shaped object in the library is graded by `ℕ ⊆ ℤ ⊆ ℂ`, so its `ℂ`-valued
`grading` field could have been relabelled by `ℤ` without loss.  Here it cannot:
`bgSVA_grading_notMem_intCast` exhibits a **nonzero** weight space at `c = 1/2`.

## Everything is at `ε = 1`

`βγ` are *commuting* fields — symplectic **bosons**.  The half-integrality lives in the conformal
weight (`h_β = h_γ = 1/2`), not in a Koszul sign.  So `par := fun _ => 0`, every `koszul` is `1`,
every `Localε` is ordinary `Local`, and the `hparity` hypothesis of `reconstructε` is the trivial
statement that filtering a `Finsupp` by a constant predicate is either the identity or zero.
This file is therefore the symplectic-fermion pipeline (`Examples/SymplecticFermionWords`,
`…Span`, `…Parity`, `…Y`, `…Instance`) with **all Koszul bookkeeping deleted** — which is exactly
the experiment: Axis A (weights) is exercised with Axis B (parity) switched off.

## Provenance of the pieces

| ingredient | source |
| --- | --- |
| `IsField`, `T`, `DCovariant`, vacuum values | `Examples.BetaGammaField` (`VOA.BG`) |
| grading, `finrank`, the `1/2` witness | `Examples.BetaGammaGrading` (`BGGrad`) |
| word fields, spanning, `Y`, VA1 | this file |

Note the orientation fix inherited from `Examples.BetaGammaField`: `Examples.BetaGamma` indexes
`beta`/`gamma` by the vertex-algebra **mode**, so the honest `z`-exponent fields are
`betaZ j = β₍₋ⱼ₋₁₎` and `gammaZ j = γ₍₋ⱼ₋₁₎`.  Those are the ones used throughout.

## The alphabet

A letter is a variable index `i : ℕ ⊕ ℕ`: `Sum.inl k` is the creation mode `β₍₋ₖ₋₁₎` and
`Sum.inr k` is `γ₍₋ₖ₋₁₎`.  Its generator field is the scaled derivative
`(k!)⁻¹ ∂_z^k βZ(z)` (resp. `γZ`), whose `z⁰`-coefficient is multiplication by `X i`.  A word is
a list of letters and creates the corresponding **monomial**; since `MvPolynomial` is spanned by
its monomials, the spanning hypothesis is three lines rather than the Clifford-algebra argument
of `Examples/SymplecticFermionSpan`.
-/

namespace VOA.BGInst

open MvPolynomial
open VOA
open VOA.Reconstruction
open VOA.BetaGamma
open VOA.BG
open VOA.BGGrad
open VOA.Reconstruction

/-! ## §1  The two base distributions, indexed by a letter

`bgBase (inl k) = βZ` and `bgBase (inr k) = γZ`: the letter records *which* field and *which*
level, but the underlying distribution only depends on the `inl`/`inr` half. -/

/-- The base distribution attached to a letter: `β` for `inl`, `γ` for `inr`. -/
noncomputable def bgBase : (ℕ ⊕ ℕ) → FormalDist (Module.End ℂ Fock)
  | Sum.inl _ => betaZ
  | Sum.inr _ => gammaZ

@[simp] theorem bgBase_inl (k : ℕ) : bgBase (Sum.inl k) = betaZ := rfl

@[simp] theorem bgBase_inr (k : ℕ) : bgBase (Sum.inr k) = gammaZ := rfl

theorem bgBase_isField (i : ℕ ⊕ ℕ) : IsField (bgBase i) := by
  cases i with
  | inl k => exact betaZ_isField
  | inr k => exact gammaZ_isField

/-- `βZ` is `ε = 1`-local with itself: `βγ` is **bosonic**. -/
theorem betaZ_localε : Localε 1 betaZ betaZ := (localε_one_iff _ _).mpr betaZ_local

theorem gammaZ_localε : Localε 1 gammaZ gammaZ := (localε_one_iff _ _).mpr gammaZ_local

theorem betaZ_gammaZ_localε : Localε 1 betaZ gammaZ :=
  (localε_one_iff _ _).mpr betaZ_gammaZ_local

theorem gammaZ_betaZ_localε : Localε 1 gammaZ betaZ :=
  Localε.symm (by norm_num) betaZ_gammaZ_localε

/-- **All four base pairings are local at `ε = 1`.**  No Koszul sign appears anywhere in this
file; that is the content of "symplectic *bosons*". -/
theorem bgBase_localε (i j : ℕ ⊕ ℕ) : Localε 1 (bgBase i) (bgBase j) := by
  cases i with
  | inl a =>
      cases j with
      | inl b => exact betaZ_localε
      | inr b => exact betaZ_gammaZ_localε
  | inr a =>
      cases j with
      | inl b => exact gammaZ_betaZ_localε
      | inr b => exact gammaZ_localε

theorem bgBase_DCovariant (i : ℕ ⊕ ℕ) : Reconstruction.DCovariant T (bgBase i) := by
  cases i with
  | inl k => exact betaZ_DCovariant
  | inr k => exact gammaZ_DCovariant

theorem bgBase_vac_neg (i : ℕ ⊕ ℕ) {q : ℤ} (hq : q < 0) : bgBase i q vac = 0 := by
  cases i with
  | inl k => exact betaZ_vac_of_neg hq
  | inr k => exact gammaZ_vac_of_neg hq

/-- The `z`-exponent-`lvl i` coefficient of the base field is multiplication by `X i`: this is
the creation mode the letter `i` names. -/
theorem bgBase_lvl (i : ℕ ⊕ ℕ) : bgBase i ((lvl i : ℕ) : ℤ) = mulX i := by
  cases i with
  | inl k =>
      change betaZ ((k : ℕ) : ℤ) = mulX (Sum.inl k)
      rw [betaZ_of_nonneg (Int.natCast_nonneg k), Int.toNat_natCast]
  | inr k =>
      change gammaZ ((k : ℕ) : ℤ) = mulX (Sum.inr k)
      rw [gammaZ_of_nonneg (Int.natCast_nonneg k), Int.toNat_natCast]

/-! ## §2  The generator fields

`bgGenField i = (k!)⁻¹ ∂_z^k (bgBase i)` with `k = lvl i`, exactly as in
`Examples/SymplecticFermionWords`; the factorial is what makes the `z⁰`-coefficient the bare
creation mode. -/

/-- The **scaled generator field** of a letter: `(k!)⁻¹ ∂_z^k βZ(z)` for `i = inl k`, and the
same with `γZ` for `i = inr k`. -/
noncomputable def bgGenField (i : ℕ ⊕ ℕ) : FormalDist (Module.End ℂ Fock) :=
  (((lvl i).factorial : ℂ))⁻¹ • (VOA.deriv^[lvl i] (bgBase i))

theorem bgGenField_isField (i : ℕ ⊕ ℕ) : IsField (bgGenField i) := by
  intro x
  obtain ⟨B, hB⟩ := (bgBase_isField i).deriv_iterate (lvl i) x
  exact ⟨B, fun n hn => by
    change (((lvl i).factorial : ℂ)⁻¹ • (VOA.deriv^[lvl i] (bgBase i)) n) x = 0
    rw [LinearMap.smul_apply, hB n hn, smul_zero]⟩

/-- **Generator fields are pairwise local at `ε = 1`**: derivatives and scalars preserve
`Localε`, and the base pairings are already at `ε = 1`. -/
theorem bgGenField_localε (i j : ℕ ⊕ ℕ) : Localε 1 (bgGenField i) (bgGenField j) := by
  have h : Localε 1 ((VOA.deriv^[lvl i]) (bgBase i))
      ((VOA.deriv^[lvl j]) (bgBase j)) :=
    ((bgBase_localε i j).deriv_iterate_left (lvl i)).deriv_iterate_right (lvl j)
  exact Localε.smul_right (by norm_num) _ (Localε.smul_left _ _ h)

theorem bgGenField_DCovariant (i : ℕ ⊕ ℕ) : Reconstruction.DCovariant T (bgGenField i) :=
  Reconstruction.DCovariant.smul (((lvl i).factorial : ℂ))⁻¹
    (Reconstruction.DCovariant.deriv_iterate (bgBase_DCovariant i) (lvl i))

/-- The generator field annihilates the vacuum below degree `0`.  Either the shifted base index
is still negative (so the base mode kills the vacuum), or the rising factorial from `∂^k` has a
vanishing factor. -/
theorem bgGenField_vacuum_neg (i : ℕ ⊕ ℕ) {q : ℤ} (hq : q < 0) : bgGenField i q vac = 0 := by
  change (((lvl i).factorial : ℂ)⁻¹ • (VOA.deriv^[lvl i] (bgBase i)) q) vac = 0
  rw [VertexOperatorAlgebra.deriv_pow_apply,
    ← Int.cast_smul_eq_zsmul ℂ (∏ m ∈ Finset.range (lvl i), (q + 1 + (m : ℤ)))]
  simp only [LinearMap.smul_apply]
  by_cases hqi : q + ((lvl i : ℕ) : ℤ) < 0
  · rw [bgBase_vac_neg i hqi, smul_zero, smul_zero]
  · rw [Finset.prod_eq_zero (i := (-q - 1).toNat) (Finset.mem_range.mpr (by omega))
        (by rw [show ((-q - 1).toNat : ℤ) = -q - 1 from by omega]; ring),
      Int.cast_zero, zero_smul, smul_zero]

/-- The `z⁰`-coefficient of the generator field is the base field at index `lvl i`: the factorial
cancels against the falling factorial produced by `∂^k`. -/
theorem bgGenField_zero (i : ℕ ⊕ ℕ) : (bgGenField i) 0 = bgBase i ((lvl i : ℕ) : ℤ) := by
  change (((lvl i).factorial : ℂ))⁻¹ • ((VOA.deriv^[lvl i] (bgBase i)) 0) = _
  rw [VertexOperatorAlgebra.deriv_pow_apply,
    show (∏ m ∈ Finset.range (lvl i), ((0 : ℤ) + 1 + (m : ℤ))) = ((lvl i).factorial : ℤ) from by
        rw [← VertexOperatorAlgebra.prod_one_add_factorial]
        exact Finset.prod_congr rfl (fun m _ => by ring),
    ← Int.cast_smul_eq_zsmul ℂ ((lvl i).factorial : ℤ), Int.cast_natCast, smul_smul,
    inv_mul_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero (lvl i)), one_smul,
    show (0 : ℤ) + ((lvl i : ℕ) : ℤ) = ((lvl i : ℕ) : ℤ) from by ring]

/-- **The generator field of the letter `i` creates the variable `X i`**: its `z⁰`-coefficient
is multiplication by `X i`. -/
theorem bgGenField_zero_mulX (i : ℕ ⊕ ℕ) : (bgGenField i) 0 = mulX i := by
  rw [bgGenField_zero, bgBase_lvl]

/-! ## §3  Word fields

A word is a list of letters; its field is the iterated normal-ordered product, taken at `ε = 1`
throughout.  Compare `Examples/SymplecticFermionWords`, where the same recursion carries a
`koszul 1 (length rest)` at every step. -/

/-- A word in the `βγ` creation letters. -/
abbrev BGWord : Type := List (ℕ ⊕ ℕ)

/-- The iterated normal-ordered product over a word, bundled with its field witness. -/
noncomputable def YwordBGF : BGWord → { f : FormalDist (Module.End ℂ Fock) // IsField f }
  | [] => ⟨idField, idField_isField⟩
  | (p :: rest) =>
      let q := YwordBGF rest
      ⟨nprodε 1 (bgGenField_isField p) q.2, IsField.nprodε _ (bgGenField_isField p) q.2⟩

/-- The word field. -/
noncomputable def YwordBG (l : BGWord) : FormalDist (Module.End ℂ Fock) := (YwordBGF l).1

theorem YwordBG_isField (l : BGWord) : IsField (YwordBG l) := (YwordBGF l).2

@[simp] theorem YwordBG_nil : YwordBG [] = idField := rfl

theorem YwordBG_cons (p : ℕ ⊕ ℕ) (rest : BGWord) :
    YwordBG (p :: rest) = nprodε 1 (bgGenField_isField p) (YwordBG_isField rest) := rfl

/-- The **creation monomial** a word field produces from the vacuum: the product of its letters'
variables.  On a polynomial algebra this is literally a monomial. -/
noncomputable def stWordBG : BGWord → Fock
  | [] => 1
  | (p :: rest) => (X p : Fock) * stWordBG rest

@[simp] theorem stWordBG_nil : stWordBG [] = (1 : Fock) := rfl

theorem stWordBG_cons (p : ℕ ⊕ ℕ) (rest : BGWord) :
    stWordBG (p :: rest) = (X p : Fock) * stWordBG rest := rfl

/-- A generator field is local with every word field — Dong's lemma, at `ε = 1`. -/
theorem bgGenField_localε_Yword (i : ℕ ⊕ ℕ) :
    ∀ l : BGWord, Localε 1 (bgGenField i) (YwordBG l)
  | [] => by
      rw [YwordBG_nil]
      exact (localε_one_iff _ _).mpr (Local_idField_right (bgGenField i))
  | (p :: rest) => by
      have ih := bgGenField_localε_Yword i rest
      have hstep : Localε ((1 : ℂ) * 1) (YwordBG (p :: rest)) (bgGenField i) := by
        rw [YwordBG_cons]
        exact dong_negε (by norm_num) (bgGenField_isField p) (YwordBG_isField rest)
          (bgGenField_localε_Yword p rest) (bgGenField_localε p i)
          (Localε.symm (by norm_num) ih)
      rw [one_mul] at hstep
      exact Localε.symm (by norm_num) hstep

/-- **Word fields are pairwise local**, with **no** sign: `Localε 1` is ordinary `Local`. -/
theorem YwordBG_localε : ∀ l₁ l₂ : BGWord, Localε 1 (YwordBG l₁) (YwordBG l₂)
  | [], l₂ => by
      rw [YwordBG_nil]
      exact (localε_one_iff _ _).mpr (Local_idField_left (YwordBG l₂))
  | (p :: rest), l₂ => by
      have hstep : Localε ((1 : ℂ) * 1) (YwordBG (p :: rest)) (YwordBG l₂) := by
        rw [YwordBG_cons]
        exact dong_negε (by norm_num) (bgGenField_isField p) (YwordBG_isField rest)
          (bgGenField_localε_Yword p rest) (bgGenField_localε_Yword p l₂)
          (YwordBG_localε rest l₂)
      rwa [one_mul] at hstep

/-- Restated as ordinary locality, which is what `βγ` being bosonic means. -/
theorem YwordBG_local (l₁ l₂ : BGWord) : Local (YwordBG l₁) (YwordBG l₂) :=
  (localε_one_iff _ _).mp (YwordBG_localε l₁ l₂)

/-- The identity field is `T`-covariant for any `T`. -/
theorem DCovariant_idField (S : Module.End ℂ Fock) :
    Reconstruction.DCovariant S (idField : FormalDist (Module.End ℂ Fock)) := by
  intro m
  by_cases h0 : m = 0
  · subst h0
    have e1 : (idField : FormalDist (Module.End ℂ Fock)) 0 = 1 := by
      rw [idField_apply, if_pos rfl]; rfl
    have e2 : (idField : FormalDist (Module.End ℂ Fock)) ((0 : ℤ) + 1) = 0 := by
      rw [idField_apply, if_neg (by norm_num)]
    rw [e1, e2, mul_one, one_mul, sub_self]
    simp
  · have e1 : (idField : FormalDist (Module.End ℂ Fock)) m = 0 := by
      rw [idField_apply, if_neg h0]
    by_cases h1 : m + 1 = 0
    · rw [e1, mul_zero, zero_mul, sub_zero, h1, zero_smul]
    · have e2 : (idField : FormalDist (Module.End ℂ Fock)) (m + 1) = 0 := by
        rw [idField_apply, if_neg h1]
      rw [e1, e2, mul_zero, zero_mul, sub_zero]
      simp

theorem YwordBG_DCovariant : ∀ l : BGWord, Reconstruction.DCovariant T (YwordBG l)
  | [] => by rw [YwordBG_nil]; exact DCovariant_idField T
  | (p :: rest) => by
      rw [YwordBG_cons]
      exact DCovariant.nprodε _ (bgGenField_isField p) (YwordBG_isField rest)
        (bgGenField_DCovariant p) (YwordBG_DCovariant rest)

/-! ### The creation tower -/

/-- **Creation tower (power-series part)**: `(YwordBG l)_q |0⟩ = 0` for `q < 0`. -/
theorem YwordBG_vacuum_neg (l : BGWord) : ∀ {q : ℤ}, q < 0 → (YwordBG l) q vac = 0 := by
  induction l with
  | nil =>
      intro q hq
      rw [YwordBG_nil]
      change (if q = 0 then (LinearMap.id : Module.End ℂ Fock) else 0) vac = 0
      rw [if_neg (by omega : ¬ q = 0)]; rfl
  | cons p rest ih =>
      intro q hq
      rw [YwordBG_cons]
      exact nprodε_vacuum_neg_gen _ (bgGenField_isField p) (YwordBG_isField rest)
        vac (fun s hs => bgGenField_vacuum_neg p hs) (fun s hs => ih hs) hq

/-- **Creation tower (base)**: the word field creates its monomial from the vacuum. -/
theorem YwordBG_vacuum_base (l : BGWord) : (YwordBG l) 0 vac = stWordBG l := by
  induction l with
  | nil =>
      rw [YwordBG_nil]
      change (if (0 : ℤ) = 0 then (LinearMap.id : Module.End ℂ Fock) else 0) vac = stWordBG []
      rw [if_pos rfl]; rfl
  | cons p rest ih =>
      rw [YwordBG_cons,
        nprodε_vacuum_base_gen _ (bgGenField_isField p) (YwordBG_isField rest)
          vac (fun s hs => bgGenField_vacuum_neg p hs)
          (fun s hs => YwordBG_vacuum_neg rest hs),
        ih, bgGenField_zero_mulX, mulX_apply, stWordBG_cons]

/-! ## §4  Spanning: the creation monomials exhaust the Fock space

For a *polynomial* algebra this is three lines: `MvPolynomial.induction_on` peels off one variable
at a time, and the word span is closed under multiplication by a variable almost by definition
(`stWordBG (p :: rest) = X p * stWordBG rest`).  Contrast `Examples/SymplecticFermionSpan`, where
the exterior algebra forces a detour through `CliffordAlgebra.iSup_ι_range_eq_top`. -/

/-- The span of the creation monomials. -/
noncomputable def stSpanBG : Submodule ℂ Fock := Submodule.span ℂ (Set.range stWordBG)

theorem stWordBG_mem (l : BGWord) : stWordBG l ∈ stSpanBG := Submodule.subset_span ⟨l, rfl⟩

theorem one_mem_stSpanBG : (1 : Fock) ∈ stSpanBG := by
  have h : stWordBG [] ∈ stSpanBG := stWordBG_mem []
  rwa [stWordBG_nil] at h

/-- **Closure under one creation operator**: on a word, `x ↦ X i * x` is `cons i`. -/
theorem X_mul_mem_stSpanBG (i : ℕ ⊕ ℕ) {x : Fock} (hx : x ∈ stSpanBG) :
    (X i : Fock) * x ∈ stSpanBG := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨l, rfl⟩ := hy
      rw [← stWordBG_cons]
      exact stWordBG_mem (i :: l)
  | zero => rw [mul_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [mul_add]; exact Submodule.add_mem _ hy hz
  | smul c y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hy

/-- **Every polynomial is a combination of creation monomials.**  `MvPolynomial.induction_on`
peels off one variable at a time; commutativity turns the right multiplication it produces into
the left multiplication the words are built by. -/
theorem mem_stSpanBG (p : Fock) : p ∈ stSpanBG := by
  induction p using MvPolynomial.induction_on with
  | C a =>
      rw [MvPolynomial.C_eq_smul_one]
      exact Submodule.smul_mem _ _ one_mem_stSpanBG
  | add p q hp hq => exact Submodule.add_mem _ hp hq
  | mul_X p i hp =>
      rw [mul_comm]
      exact X_mul_mem_stSpanBG i hp

theorem stSpanBG_eq_top : stSpanBG = ⊤ := eq_top_iff.mpr fun p _ => mem_stSpanBG p

/-- **The creation monomials span the `βγ` Fock space** — the `hspan` hypothesis of
`reconstructε`. -/
theorem stWordBG_span : Submodule.span ℂ (Set.range stWordBG) = (⊤ : Submodule ℂ Fock) :=
  stSpanBG_eq_top

theorem stWordBG_surjective : Function.Surjective (Finsupp.linearCombination ℂ stWordBG) := by
  rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination, stWordBG_span]

/-! ## §5  The parity hypothesis is trivial

`βγ` is purely even, so `par := fun _ => 0` is a constant function and `Finsupp.filter` by
`par i = p` is either the identity (when `p = 0`) or the zero map.  This is the whole of
`hparity`; compare `Examples/SymplecticFermionParity`, where the length parity of a word has to be
matched against the Clifford `ℤ/2`-grading. -/

/-- The (constant, even) parity function on words. -/
def bgPar : BGWord → ZMod 2 := fun _ => 0

/-- **`hparity`, trivially.**  Filtering by a constant predicate keeps everything or nothing. -/
theorem stWordBG_parity_split (c : BGWord →₀ ℂ)
    (hc : Finsupp.linearCombination ℂ stWordBG c = 0) (p : ZMod 2) :
    Finsupp.linearCombination ℂ stWordBG (c.filter (fun i => bgPar i = p)) = 0 := by
  classical
  by_cases hp : (0 : ZMod 2) = p
  · have hfil : c.filter (fun i => bgPar i = p) = c := by
      refine Finsupp.ext fun i => ?_
      rw [Finsupp.filter_apply, if_pos (show bgPar i = p from hp)]
    rw [hfil, hc]
  · have hfil : c.filter (fun i => bgPar i = p) = 0 := by
      refine Finsupp.ext fun i => ?_
      rw [Finsupp.filter_apply, if_neg (show ¬ (bgPar i = p) from hp), Finsupp.zero_apply]
    rw [hfil, map_zero]

/-! ## §6  The vertex operator `YBG`

`reconstructε` with `par := bgPar` constant `0`.  Every Koszul sign in its conclusion is
`koszul 0 0 = 1`, so the locality conjunct is ordinary locality for *arbitrary* pairs of states —
no parity-homogeneity side condition survives. -/

/-- **The `βγ` vertex operator exists.**  `reconstructε` applied to the word fields, with the
purely even parity `bgPar`. -/
theorem YBG_exists :
    ∃ YA : Fock →ₗ[ℂ] FormalDist (Module.End ℂ Fock),
      (∀ l : BGWord, YA (stWordBG l) = YwordBG l) ∧
      (∀ u : Fock, IsField (YA u)) ∧
      (∀ (p q : ZMod 2) (c d : BGWord →₀ ℂ),
          (∀ i ∈ c.support, bgPar i = p) → (∀ j ∈ d.support, bgPar j = q) →
          Localε (koszul p q) (YA (Finsupp.linearCombination ℂ stWordBG c))
            (YA (Finsupp.linearCombination ℂ stWordBG d))) ∧
      (∀ u : Fock, (YA u) 0 vac = u) ∧
      (∀ u : Fock, ∀ q : ℤ, q < 0 → (YA u) q vac = 0) ∧
      (∀ u : Fock, Reconstruction.DCovariant T (YA u)) :=
  reconstructε vac stWordBG YwordBG T bgPar
    stWordBG_span stWordBG_parity_split YwordBG_isField
    (fun l₁ l₂ => by
      rw [show koszul (bgPar l₁) (bgPar l₂) = 1 from koszul_zero_left 0]
      exact YwordBG_localε l₁ l₂)
    YwordBG_vacuum_base (fun l _q hq => YwordBG_vacuum_neg l hq)
    T_vac YwordBG_DCovariant

/-- **The vertex operator of the `βγ` vertex algebra**, defined on all of the Fock space. -/
noncomputable def YBG : Fock →ₗ[ℂ] FormalDist (Module.End ℂ Fock) := YBG_exists.choose

/-- `YBG` restricts to the word fields on the creation monomials. -/
theorem YBG_word (l : BGWord) : YBG (stWordBG l) = YwordBG l := YBG_exists.choose_spec.1 l

theorem YBG_isField (u : Fock) : IsField (YBG u) := YBG_exists.choose_spec.2.1 u

theorem YBG_localε (p q : ZMod 2) (c d : BGWord →₀ ℂ)
    (hc : ∀ i ∈ c.support, bgPar i = p) (hd : ∀ j ∈ d.support, bgPar j = q) :
    Localε (koszul p q) (YBG (Finsupp.linearCombination ℂ stWordBG c))
      (YBG (Finsupp.linearCombination ℂ stWordBG d)) :=
  YBG_exists.choose_spec.2.2.1 p q c d hc hd

theorem YBG_creation (u : Fock) : (YBG u) 0 vac = u := YBG_exists.choose_spec.2.2.2.1 u

theorem YBG_creation_neg (u : Fock) {q : ℤ} (hq : q < 0) : (YBG u) q vac = 0 :=
  YBG_exists.choose_spec.2.2.2.2.1 u q hq

theorem YBG_DCovariant (u : Fock) : Reconstruction.DCovariant T (YBG u) :=
  YBG_exists.choose_spec.2.2.2.2.2 u

/-- **Unrestricted locality.**  Because the parity is constant, the parity-homogeneity side
condition of `reconstructε`'s locality conjunct is vacuous: *any* two states have mutually local
vertex operators, at `ε = 1`.  This is the concrete form of "`βγ` is an ordinary (bosonic) vertex
algebra that merely happens to have half-integer weights". -/
theorem YBG_local (u v : Fock) : Local (YBG u) (YBG v) := by
  obtain ⟨c, rfl⟩ := stWordBG_surjective u
  obtain ⟨d, rfl⟩ := stWordBG_surjective v
  have h := YBG_localε 0 0 c d (fun i _ => rfl) (fun j _ => rfl)
  rw [show koszul (0 : ZMod 2) 0 = 1 from koszul_zero_left 0, localε_one_iff] at h
  exact h

/-- The vacuum's vertex operator is the identity field. -/
theorem YBG_vacuum : YBG vac = idField := by
  have h := YBG_word []
  rw [stWordBG_nil, YwordBG_nil] at h
  exact h

/-- The unit of `FormalDist` is the identity field (the right-hand side of VA2). -/
theorem idFieldBG_eq_one : (idField : FormalDist (Module.End ℂ Fock)) = 1 := by
  funext j
  rw [idField_apply, FormalDist.one_apply]
  rfl

/-! ## §7  VA1: the vertex operators are graded fields

The propagation argument of `Examples/SymplecticFermionInstance` §§3–5, with the parity half
deleted.  `WtFieldBG f D` says the `zʲ`-coefficient of `f` raises the conformal weight by
`D + j`; setting `j = -n-1` turns it into `u₍ₙ₎ : 𝒱_w → 𝒱_{D+w-n-1}`, which is VA1. -/

/-- A **graded field of conformal weight `D`**: the `zʲ`-coefficient sends `𝒱_w` into
`𝒱_{D+w+j}`. -/
def WtFieldBG (f : FormalDist (Module.End ℂ Fock)) (D : ℂ) : Prop :=
  ∀ (j : ℤ) (w : ℂ) (x : Fock), x ∈ gradingBG w → f j x ∈ gradingBG (D + w + (j : ℂ))

/-- **`βZ(z)` is a graded field of conformal weight `1/2`** — the half-integer, in field form.
Read off from `BGGrad.beta_mem_gradingBG` through the reindexing `βZ j = β₍₋ⱼ₋₁₎`. -/
theorem betaZ_WtField : WtFieldBG betaZ (1 / 2) := by
  intro j w x hx
  rw [betaZ_eq]
  have h := beta_mem_gradingBG hx (-j - 1)
  rwa [show w - (((-j - 1 : ℤ)) : ℂ) - 1 / 2 = 1 / 2 + w + (j : ℂ) from by push_cast; ring] at h

/-- **`γZ(z)` is a graded field of conformal weight `1/2`.** -/
theorem gammaZ_WtField : WtFieldBG gammaZ (1 / 2) := by
  intro j w x hx
  rw [gammaZ_eq]
  have h := gamma_mem_gradingBG hx (-j - 1)
  rwa [show w - (((-j - 1 : ℤ)) : ℂ) - 1 / 2 = 1 / 2 + w + (j : ℂ) from by push_cast; ring] at h

theorem bgBase_WtField (i : ℕ ⊕ ℕ) : WtFieldBG (bgBase i) (1 / 2) := by
  cases i with
  | inl k => exact betaZ_WtField
  | inr k => exact gammaZ_WtField

/-- `bgWt` is `lvl + 1/2`: the two files' bookkeeping for the level agrees definitionally. -/
theorem bgWt_eq_lvl (i : ℕ ⊕ ℕ) : bgWt i = ((lvl i : ℕ) : ℂ) + 1 / 2 := rfl

/-- **The generator field of the letter `i` has conformal weight `bgWt i = lvl i + 1/2`.**
Each `∂_z` raises the weight by one, starting from the base weight `1/2`. -/
theorem bgGenField_WtField (i : ℕ ⊕ ℕ) : WtFieldBG (bgGenField i) (bgWt i) := by
  intro j w x hx
  change (((lvl i).factorial : ℂ)⁻¹ • (VOA.deriv^[lvl i] (bgBase i)) j) x ∈ _
  rw [LinearMap.smul_apply]
  refine Submodule.smul_mem _ _ ?_
  rw [VertexOperatorAlgebra.deriv_pow_apply,
    ← Int.cast_smul_eq_zsmul ℂ (∏ m ∈ Finset.range (lvl i), (j + 1 + (m : ℤ))),
    LinearMap.smul_apply]
  refine Submodule.smul_mem _ _ ?_
  rw [bgWt_eq_lvl, show ((lvl i : ℕ) : ℂ) + 1 / 2 + w + ((j : ℤ) : ℂ)
      = 1 / 2 + w + (((j + ((lvl i : ℕ) : ℤ)) : ℤ) : ℂ) from by push_cast; ring]
  exact bgBase_WtField i (j + ((lvl i : ℕ) : ℤ)) w x hx

theorem idFieldBG_WtField : WtFieldBG idField 0 := by
  intro j w x hx
  rw [idField_apply]
  by_cases hj : j = 0
  · subst hj
    rw [if_pos rfl, LinearMap.id_apply,
      show (0 : ℂ) + w + (((0 : ℤ)) : ℂ) = w from by push_cast; ring]
    exact hx
  · rw [if_neg hj, LinearMap.zero_apply]
    exact Submodule.zero_mem _

/-- A finite-support `finsum` of elements of a submodule lies in the submodule. -/
theorem finsum_mem_submodule {ι : Type*} (S : Submodule ℂ Fock) (g : ι → Fock)
    (hfin : (Function.support g).Finite) (hmem : ∀ i, g i ∈ S) : (∑ᶠ i, g i) ∈ S := by
  rw [finsum_eq_finsetSum_of_support_subset g (s := hfin.toFinset) (by rw [hfin.coe_toFinset])]
  exact Submodule.sum_mem _ (fun i _ => hmem i)

/-- **Weights add under the normal-ordered product.**  Each summand of `:a(z)b(z):` composes
the shifts `Da + m` and `Db + (s - m)`, and the `m` cancels. -/
theorem WtFieldBG.nprod (ε : ℂ) {a b : FormalDist (Module.End ℂ Fock)} (ha : IsField a)
    (hb : IsField b) {Da Db : ℂ} (hga : WtFieldBG a Da) (hgb : WtFieldBG b Db) :
    WtFieldBG (nprodε ε ha hb) (Da + Db) := by
  intro s w x hx
  rw [nprodε_apply]
  refine finsum_mem_submodule _ _ (normalOrderedε_diag_support_finite ε ha hb s x) (fun m => ?_)
  rw [normalOrderedε_apply]
  by_cases h0 : 0 ≤ m
  · rw [if_pos h0]
    change a m (b (s - m) x) ∈ _
    have hb' := hgb (s - m) w x hx
    have ha' := hga m (Db + w + (((s - m : ℤ)) : ℂ)) _ hb'
    rwa [show Da + (Db + w + (((s - m : ℤ)) : ℂ)) + ((m : ℤ) : ℂ)
        = Da + Db + w + ((s : ℤ) : ℂ) from by push_cast; ring] at ha'
  · rw [if_neg h0, LinearMap.smul_apply]
    refine Submodule.smul_mem _ _ ?_
    change b (s - m) (a m x) ∈ _
    have ha' := hga m w x hx
    have hb' := hgb (s - m) (Da + w + ((m : ℤ) : ℂ)) _ ha'
    rwa [show Db + (Da + w + ((m : ℤ) : ℂ)) + (((s - m : ℤ)) : ℂ)
        = Da + Db + w + ((s : ℤ) : ℂ) from by push_cast; ring] at hb'

/-- The conformal weight of a word: the sum of the weights of its letters.  Every letter carries a
**half**-integer, so a word of odd length carries a half-integer total. -/
noncomputable def bgWeight : BGWord → ℂ
  | [] => 0
  | (p :: rest) => bgWt p + bgWeight rest

@[simp] theorem bgWeight_nil : bgWeight [] = 0 := rfl

theorem bgWeight_cons (p : ℕ ⊕ ℕ) (rest : BGWord) :
    bgWeight (p :: rest) = bgWt p + bgWeight rest := rfl

/-- **The word field of `l` is a graded field of the weight of `l`** — VA1 for the spanning
family. -/
theorem YwordBG_WtField (l : BGWord) : WtFieldBG (YwordBG l) (bgWeight l) := by
  induction l with
  | nil => rw [YwordBG_nil, bgWeight_nil]; exact idFieldBG_WtField
  | cons p rest ih =>
      rw [YwordBG_cons, bgWeight_cons]
      exact WtFieldBG.nprod _ (bgGenField_isField p) (YwordBG_isField rest)
        (bgGenField_WtField p) ih

/-! ### Words and monomials

`gradingBG c` is (by `Examples/BetaGammaGrading`) contained in the span of the weight-`c`
monomials, so the transfer needs each monomial to *be* a word state.  On a polynomial algebra that
is a bookkeeping induction over the exponent vector. -/

theorem stWordBG_append (l₁ l₂ : BGWord) :
    stWordBG (l₁ ++ l₂) = stWordBG l₁ * stWordBG l₂ := by
  induction l₁ with
  | nil => rw [List.nil_append, stWordBG_nil, one_mul]
  | cons p rest ih => rw [List.cons_append, stWordBG_cons, stWordBG_cons, ih, mul_assoc]

theorem stWordBG_replicate (n : ℕ) (i : ℕ ⊕ ℕ) :
    stWordBG (List.replicate n i) = (X i : Fock) ^ n := by
  induction n with
  | zero => rw [List.replicate_zero, stWordBG_nil, pow_zero]
  | succ m ih => rw [List.replicate_succ, stWordBG_cons, ih, pow_succ']

theorem bgWeight_append (l₁ l₂ : BGWord) :
    bgWeight (l₁ ++ l₂) = bgWeight l₁ + bgWeight l₂ := by
  induction l₁ with
  | nil => rw [List.nil_append, bgWeight_nil, zero_add]
  | cons p rest ih => rw [List.cons_append, bgWeight_cons, bgWeight_cons, ih, add_assoc]

theorem bgWeight_replicate (n : ℕ) (i : ℕ ⊕ ℕ) :
    bgWeight (List.replicate n i) = (n : ℂ) * bgWt i := by
  induction n with
  | zero => rw [List.replicate_zero, bgWeight_nil, Nat.cast_zero, zero_mul]
  | succ m ih => rw [List.replicate_succ, bgWeight_cons, ih]; push_cast; ring

/-- **Every monomial is a word state, of the matching weight.**  Induction on the exponent
vector: a variable of multiplicity `n` contributes the sublist `replicate n i`. -/
theorem exists_word_of_monomial (d : (ℕ ⊕ ℕ) →₀ ℕ) :
    ∃ l : BGWord, stWordBG l = (monomial d 1 : Fock) ∧ bgWeight l = Finsupp.weight bgWt d := by
  classical
  induction d using Finsupp.induction with
  | zero =>
      refine ⟨[], ?_, ?_⟩
      · rw [stWordBG_nil, MvPolynomial.monomial_zero', MvPolynomial.C_1]
      · rw [bgWeight_nil, map_zero]
  | single_add i n d' _ _ ih =>
      obtain ⟨l, hl, hw⟩ := ih
      refine ⟨List.replicate n i ++ l, ?_, ?_⟩
      · rw [stWordBG_append, stWordBG_replicate, hl, MvPolynomial.X_pow_eq_monomial,
          MvPolynomial.monomial_mul, one_mul]
      · rw [bgWeight_append, bgWeight_replicate, hw, map_add, Finsupp.weight_single,
          nsmul_eq_mul]

/-! ### Transport along `YBG`

Being a graded field of weight `D` is a *linear* condition on the state, so the states satisfying
it form a submodule; it contains every weight-`D` monomial, hence all of `gradingBG D`. -/

/-- The states whose vertex operator is a graded field of weight `D`. -/
noncomputable def wtStatesBG (D : ℂ) : Submodule ℂ Fock where
  carrier := {u : Fock | WtFieldBG (YBG u) D}
  add_mem' := by
    intro u v hu hv j w x hx
    rw [map_add]
    change (YBG u) j x + (YBG v) j x ∈ _
    exact Submodule.add_mem _ (hu j w x hx) (hv j w x hx)
  zero_mem' := by
    intro j w x _
    rw [map_zero]
    change (0 : Fock) ∈ _
    exact Submodule.zero_mem _
  smul_mem' := by
    intro c u hu j w x hx
    rw [map_smul]
    change c • ((YBG u) j x) ∈ _
    exact Submodule.smul_mem _ _ (hu j w x hx)

theorem gradingBG_le_wtStatesBG (D : ℂ) : gradingBG D ≤ wtStatesBG D := by
  refine le_trans (gradingBG_le_span D) (Submodule.span_le.mpr ?_)
  rintro _ ⟨d, hd, rfl⟩
  have hdw : Finsupp.weight bgWt d = D := hd
  obtain ⟨l, hl, hw⟩ := exists_word_of_monomial d
  have hmem : stWordBG l ∈ wtStatesBG D := by
    change WtFieldBG (YBG (stWordBG l)) D
    rw [YBG_word l, ← hdw, ← hw]
    exact YwordBG_WtField l
  rw [hl] at hmem
  exact hmem

/-- **VA1, field form**: the vertex operator of a weight-`h` state is a graded field of
weight `h`. -/
theorem YBG_WtField {h : ℂ} {u : Fock} (hu : u ∈ gradingBG h) : WtFieldBG (YBG u) h :=
  gradingBG_le_wtStatesBG h hu

/-! ## §8  The instance -/

/-- **The `βγ` super vertex algebra.**

The library's **first** `SuperVertexAlgebra` whose weight grading takes a non-integer value on a
nonzero subspace (`bgSVA_grading_notMem_intCast` below).  Its parity is trivial — `βγ` are
commuting fields — so every Koszul sign is `1` and VA4 is ordinary locality; that is the point:
Axis A (the `ℂ`-valued grading) is exercised here with Axis B (parity) switched off. -/
noncomputable def bgSVA : SuperVertexAlgebra Fock where
  grading := gradingBG
  isInternal := gradingBG_isInternal
  finrank := gradingBG_finiteDimensional
  parity := (ParityGrading.even Fock).parity
  parity_isInternal := (ParityGrading.even Fock).isInternal
  Y := YBG
  vacuum := vac
  vacuum_mem := one_mem_gradingBG
  vacuum_parity := by rw [ParityGrading.even_parity_zero]; trivial
  grading_mode := by
    intro h k u hu v hv n
    have hmode := YBG_WtField hu (-n - 1) k v hv
    rwa [show h + k + (((-n - 1 : ℤ)) : ℂ) = h + k - (n : ℂ) - 1 from by push_cast; ring] at hmode
  parity_mode := by
    intro p q u hu v hv n
    by_cases hp : p = 0
    · by_cases hq : q = 0
      · subst hp; subst hq
        rw [add_zero, ParityGrading.even_parity_zero]
        trivial
      · rw [ParityGrading.eq_zero_of_mem_even_of_ne hq hv]
        simp only [map_zero]
        exact Submodule.zero_mem _
    · rw [ParityGrading.eq_zero_of_mem_even_of_ne hp hu]
      simp only [map_zero]
      exact Submodule.zero_mem _
  vacuum_Y := by rw [YBG_vacuum, idFieldBG_eq_one]
  creation := by
    intro u
    refine ⟨?_, fun n hn => ?_⟩
    · have hidx : mode (YBG u) (-1) vac = (YBG u) 0 vac := by rw [mode_apply]; norm_num
      rw [hidx]
      exact YBG_creation u
    · rw [mode_apply]
      exact YBG_creation_neg u (by omega)
  locality := by
    intro p q u hu v hv
    by_cases hp : p = 0
    · by_cases hq : q = 0
      · subst hp; subst hq
        rw [show koszul (0 : ZMod 2) 0 = 1 from koszul_zero_left 0, localε_one_iff]
        exact YBG_local u v
      · rw [ParityGrading.eq_zero_of_mem_even_of_ne hq hv, map_zero]
        exact localε_zero_right _ _
    · rw [ParityGrading.eq_zero_of_mem_even_of_ne hp hu, map_zero]
      exact localε_zero_left _ _
  regularity := by
    intro u v
    obtain ⟨B, hB⟩ := YBG_isField u v
    refine ⟨-B, fun n hn => ?_⟩
    rw [mode_apply]
    exact hB (-n - 1) (by omega)

/-! ## §9  The instance really is the `βγ` system

Before the main theorem: the identification of the two generating **states** with the two generating
**fields**.  Without this, "`bgSVA` has a weight-`1/2` space" would only say that some abstract
vertex algebra has an odd-looking grading; with it, the weight-`1/2` state is `β₍₋₁₎𝟙` and its
vertex operator is literally `βZ(z)`. -/

@[simp] theorem bgSVA_Y : bgSVA.Y = YBG := rfl

@[simp] theorem bgSVA_vacuum : bgSVA.vacuum = vac := rfl

@[simp] theorem bgSVA_grading : bgSVA.grading = gradingBG := rfl

/-- A one-letter word field is the bare generator field: `:g(z)1(z): = g(z)`. -/
theorem YwordBG_singleton (i : ℕ ⊕ ℕ) : YwordBG [i] = bgGenField i := by
  have h : YwordBG [i]
      = nprodε 1 (bgGenField_isField i) (idField_isField (V := Fock)) := rfl
  rw [h, nprodε_one, nprod_idField]

/-- **The vertex operator of the state `X i` is the generator field of the letter `i`.** -/
theorem YBG_gen (i : ℕ ⊕ ℕ) : YBG (X i : Fock) = bgGenField i := by
  have h := YBG_word [i]
  rw [stWordBG_cons, stWordBG_nil, mul_one, YwordBG_singleton] at h
  exact h

theorem bgGenField_inl_zero : bgGenField (Sum.inl 0) = betaZ := by
  have h : bgGenField (Sum.inl 0)
      = (((0 : ℕ).factorial : ℂ))⁻¹ • (VOA.deriv^[0] (bgBase (Sum.inl 0))) := rfl
  rw [h, Function.iterate_zero_apply, bgBase_inl, Nat.factorial_zero, Nat.cast_one, inv_one,
    one_smul]

theorem bgGenField_inr_zero : bgGenField (Sum.inr 0) = gammaZ := by
  have h : bgGenField (Sum.inr 0)
      = (((0 : ℕ).factorial : ℂ))⁻¹ • (VOA.deriv^[0] (bgBase (Sum.inr 0))) := rfl
  rw [h, Function.iterate_zero_apply, bgBase_inr, Nat.factorial_zero, Nat.cast_one, inv_one,
    one_smul]

/-- **`Y(β₍₋₁₎𝟙, z) = βZ(z)`.**  The state at conformal weight `1/2` carries exactly the field
`β` of `Examples.BetaGamma` (reindexed to the `z`-exponent convention). -/
theorem bgSVA_Y_beta : bgSVA.Y (X (Sum.inl 0) : Fock) = betaZ := by
  rw [bgSVA_Y, YBG_gen, bgGenField_inl_zero]

/-- **`Y(γ₍₋₁₎𝟙, z) = γZ(z)`.** -/
theorem bgSVA_Y_gamma : bgSVA.Y (X (Sum.inr 0) : Fock) = gammaZ := by
  rw [bgSVA_Y, YBG_gen, bgGenField_inr_zero]

/-- The weight-`1/2` state is `β₍₋₁₎𝟙`, the first creation mode acting on the vacuum. -/
theorem X_inl_zero_eq_beta_vac :
    VOA.BetaGamma.beta (-1) (vac : Fock) = (X (Sum.inl 0) : Fock) := by
  have h := X_inl_eq_beta_vacuum 0
  rwa [show (-((0 : ℕ) : ℤ) - 1) = (-1 : ℤ) from by norm_num] at h

/-! ## §10  The main theorem: a genuinely non-integer conformal weight

Every earlier weight grading in the library takes values in `ℕ ⊆ ℤ ⊆ ℂ`, so the `ℂ`-valued index
of `SuperVertexAlgebra.grading` could have been replaced by `ℤ` without losing anything.  Here it
could not: the state `β₍₋₁₎𝟙` is nonzero and sits at weight `1/2`. -/

/-- The witness state is nonzero. -/
theorem beta_vac_ne_zero : (X (Sum.inl 0) : Fock) ≠ 0 := X_inl_zero_ne_zero

/-- The witness state has conformal weight `1/2` in `bgSVA`. -/
theorem beta_vac_mem_half : (X (Sum.inl 0) : Fock) ∈ bgSVA.grading (1 / 2) :=
  X_inl_zero_mem_half

/-- **THE POINT OF THE TRACK.**  `bgSVA` is a `SuperVertexAlgebra` with a **nonzero** weight
space at a weight that is not the image of any integer.  Hence its `ℂ`-valued grading is not a
relabelled `ℤ`-grading, and `SuperVertexAlgebra.grading : ℂ → Submodule ℂ 𝒱` is exercised at a
non-integer weight for the first time.  The witness is `β₍₋₁₎𝟙` at weight `1/2`. -/
theorem bgSVA_grading_notMem_intCast :
    ∃ c : ℂ, bgSVA.grading c ≠ ⊥ ∧ ∀ n : ℤ, (n : ℂ) ≠ c :=
  ⟨1 / 2, gradingBG_half_ne_bot, half_ne_intCast⟩

/-- The same, with the witness state spelled out: a nonzero vector, its weight, and the proof
that the weight is not an integer. -/
theorem bgSVA_half_weight_witness :
    (X (Sum.inl 0) : Fock) ≠ 0 ∧ (X (Sum.inl 0) : Fock) ∈ bgSVA.grading (1 / 2)
      ∧ ∀ n : ℤ, (n : ℂ) ≠ (1 / 2 : ℂ) :=
  ⟨beta_vac_ne_zero, beta_vac_mem_half, half_ne_intCast⟩

/-- **Not one exceptional weight but infinitely many.**  Every `k + 1/2` is occupied, so no
reindexing of the grading by `ℤ` is possible even in principle. -/
theorem bgSVA_grading_half_succ_ne_bot (k : ℕ) : bgSVA.grading ((k : ℂ) + 1 / 2) ≠ ⊥ :=
  gradingBG_half_succ_ne_bot k

/-- **`bgSVA` is purely even.**  Every state is even, so every Koszul sign is `1` and VA4 is
ordinary locality (`YBG_local`).  This is Axis B switched off. -/
theorem bgSVA_parity_zero : bgSVA.parity 0 = ⊤ := ParityGrading.even_parity_zero

theorem bgSVA_parity_one : bgSVA.parity 1 = ⊥ :=
  ParityGrading.even_parity_of_ne (𝒱 := Fock) (p := 1) (by decide)

theorem bgSVA_mem_parity_zero (u : Fock) : u ∈ bgSVA.parity 0 := by
  rw [bgSVA_parity_zero]; trivial

/-- **Spin–statistics fails for `βγ`, in the direction opposite to symplectic fermions.**

`SuperVertexAlgebra` deliberately keeps `grading` and `parity` unlinked.  Symplectic fermions
break the link one way (odd states of *integer* weight); `βγ` breaks it the other way — the state
`β₍₋₁₎𝟙` is **even** and of **non-integer** weight `1/2`.  Together the two examples show that
neither implication of `SpinStatistics` is derivable from the axioms. -/
theorem bgSVA_not_spinStatistics : ¬ SpinStatistics bgSVA := by
  intro hss
  have h := hss (1 / 2) 0 (X (Sum.inl 0) : Fock) beta_vac_ne_zero beta_vac_mem_half
    (bgSVA_mem_parity_zero _)
  obtain ⟨m, hm⟩ := h.mpr rfl
  exact half_ne_intCast m hm



/-! ## §11  The conformal vector

The state `ω` of `Examples/BetaGammaVirasoro` — where the central charge `c = -1` is *derived* —
realized inside `bgSVA`, together with the **explicit** vertex operator it carries.  That operator
is the energy–momentum tensor of the `λ = 1/2` `βγ` system,

  `T(z) = ½ :β(z) ∂γ(z): - ½ :∂β(z) γ(z):`,

and it comes out of the abstract reconstruction `YBG` by pure unwinding: `ω` is a combination of
two two-letter words, and a two-letter word field is a normal-ordered product of two generator
fields.

What is **not** claimed here is the `SuperNearVOA` instance; see §12 for exactly what is missing.
-/

/-- Every word state is homogeneous of the weight of its word. -/
theorem stWordBG_mem_gradingBG (l : BGWord) : stWordBG l ∈ gradingBG (bgWeight l) := by
  induction l with
  | nil => rw [stWordBG_nil, bgWeight_nil]; exact one_mem_gradingBG
  | cons p rest ih =>
      rw [stWordBG_cons, bgWeight_cons]
      exact mem_gradingBG.mpr
        ((MvPolynomial.isWeightedHomogeneous_X ℂ bgWt p).mul (mem_gradingBG.mp ih))

/-- **The conformal vector**, as a combination of two creation monomials.  Each term pairs a
weight-`1/2` mode with a weight-`3/2` mode: *two half-integers summing to the integer `2`*.  The
antisymmetric two-term shape is exactly what half-integer moding produces — contrast the
symplectic-fermion `ω = χ⁻₋₁χ⁺₋₁𝟙`, a single `1 + 1` term. -/
noncomputable def bgOmega : Fock :=
  (1 / 2 : ℂ) • stWordBG [Sum.inl 0, Sum.inr 1]
    - (1 / 2 : ℂ) • stWordBG [Sum.inl 1, Sum.inr 0]

theorem bgOmega_eq :
    bgOmega = (1 / 2 : ℂ) • (X (Sum.inl 0) * X (Sum.inr 1) : Fock)
      - (1 / 2 : ℂ) • (X (Sum.inl 1) * X (Sum.inr 0) : Fock) := by
  simp only [bgOmega, stWordBG_cons, stWordBG_nil, mul_one]

/-- **It is the very state whose modes `Examples/BetaGammaVirasoro` proved to satisfy the
Virasoro relations at `c = -1`.**  So the conformal vector of `bgSVA` is not a fresh guess: it is
`L₋₂𝟙` for the `Lₙ` whose central charge was derived there. -/
theorem bgOmega_eq_BGVir : bgOmega = BGVir.omegaBG := by
  rw [bgOmega_eq, BGVir.omegaBG_eq]

theorem bgWeight_omega_word_left : bgWeight [Sum.inl 0, Sum.inr 1] = 2 := by
  rw [bgWeight_cons, bgWeight_cons, bgWeight_nil, bgWt_inl, bgWt_inr]
  push_cast
  ring

theorem bgWeight_omega_word_right : bgWeight [Sum.inl 1, Sum.inr 0] = 2 := by
  rw [bgWeight_cons, bgWeight_cons, bgWeight_nil, bgWt_inl, bgWt_inr]
  push_cast
  ring

/-- **`ω` has conformal weight `2`** — the `conformal_mem` field of `SuperNearVOA`. -/
theorem bgOmega_mem_grading_two : bgOmega ∈ bgSVA.grading 2 := by
  refine Submodule.sub_mem _ (Submodule.smul_mem _ _ ?_) (Submodule.smul_mem _ _ ?_)
  · rw [← bgWeight_omega_word_left]; exact stWordBG_mem_gradingBG _
  · rw [← bgWeight_omega_word_right]; exact stWordBG_mem_gradingBG _

/-- **`ω` is even** — the `conformal_parity` field of `SuperNearVOA`.  Trivially, since `bgSVA` is
purely even. -/
theorem bgOmega_mem_parity_zero : bgOmega ∈ bgSVA.parity 0 := bgSVA_mem_parity_zero _

/-- `nprodε` depends only on the underlying distributions, not on the `IsField` witnesses — the
right-slot companion of `Core.Reconstruction.nprod_congr`. -/
theorem nprodε_congr_right {ε : ℂ} {a b b' : FormalDist (Module.End ℂ Fock)} (ha : IsField a)
    (hb : IsField b) (hb' : IsField b') (h : b = b') :
    nprodε ε ha hb = nprodε ε ha hb' := by
  subst h; rfl

/-- A two-letter word field is the (bosonic) normal-ordered product of the two generator fields:
the trailing `idField` in the recursion is absorbed by `nprod_idField`. -/
theorem YwordBG_pair (i j : ℕ ⊕ ℕ) :
    YwordBG [i, j] = nprod (bgGenField_isField i) (bgGenField_isField j) := by
  have h1 : YwordBG [i, j] = nprodε 1 (bgGenField_isField i) (YwordBG_isField [j]) := rfl
  rw [h1, nprodε_congr_right (ε := 1) (bgGenField_isField i) (YwordBG_isField [j])
      (bgGenField_isField j) (YwordBG_singleton j), nprodε_one]

theorem bgGenField_inl_one : bgGenField (Sum.inl 1) = VOA.deriv betaZ := by
  have h : bgGenField (Sum.inl 1)
      = (((1 : ℕ).factorial : ℂ))⁻¹ • (VOA.deriv^[1] (bgBase (Sum.inl 1))) := rfl
  rw [h, Function.iterate_one, bgBase_inl, Nat.factorial_one, Nat.cast_one, inv_one, one_smul]

theorem bgGenField_inr_one : bgGenField (Sum.inr 1) = VOA.deriv gammaZ := by
  have h : bgGenField (Sum.inr 1)
      = (((1 : ℕ).factorial : ℂ))⁻¹ • (VOA.deriv^[1] (bgBase (Sum.inr 1))) := rfl
  rw [h, Function.iterate_one, bgBase_inr, Nat.factorial_one, Nat.cast_one, inv_one, one_smul]

/-- `nprod` depends only on the underlying distributions, in both slots. -/
theorem nprod_congr₂ {a a' b b' : FormalDist (Module.End ℂ Fock)} (ha : IsField a)
    (hb : IsField b) (ha' : IsField a') (hb' : IsField b') (h1 : a = a') (h2 : b = b') :
    nprod ha hb = nprod ha' hb' := by
  subst h1; subst h2; rfl

/-- `Y(ω, z)` as a combination of the two two-letter word fields. -/
theorem YBG_bgOmega :
    YBG bgOmega
      = (1 / 2 : ℂ) • nprod (bgGenField_isField (Sum.inl 0)) (bgGenField_isField (Sum.inr 1))
        - (1 / 2 : ℂ) • nprod (bgGenField_isField (Sum.inl 1))
            (bgGenField_isField (Sum.inr 0)) := by
  rw [bgOmega, map_sub, map_smul, map_smul, YBG_word, YBG_word, YwordBG_pair, YwordBG_pair]

/-- **The energy–momentum tensor, explicitly.**

`Y(ω, z) = ½ :βZ(z) ∂γZ(z): - ½ :∂βZ(z) γZ(z):`.

The abstract vertex operator produced by `reconstructε` is, on this state, exactly the textbook
`T(z)` of the `λ = 1/2` `βγ` system — and no normalization was chosen by hand: the coefficients
`±½` come from `bgOmega`, which is `L₋₂𝟙` for the `Lₙ` of `Examples/BetaGammaVirasoro`, where the
central charge `c = -1` was derived. -/
theorem YBG_bgOmega_fields :
    YBG bgOmega
      = (1 / 2 : ℂ) • nprod betaZ_isField gammaZ_isField.deriv
        - (1 / 2 : ℂ) • nprod betaZ_isField.deriv gammaZ_isField := by
  rw [YBG_bgOmega,
    nprod_congr₂ (bgGenField_isField (Sum.inl 0)) (bgGenField_isField (Sum.inr 1))
      betaZ_isField gammaZ_isField.deriv bgGenField_inl_zero bgGenField_inr_one,
    nprod_congr₂ (bgGenField_isField (Sum.inl 1)) (bgGenField_isField (Sum.inr 0))
      betaZ_isField.deriv gammaZ_isField bgGenField_inl_one bgGenField_inr_zero]

/-! ## §12  The completed conformal upgrade

The calculation below is the proof roadmap for the `SuperNearVOA` and CFT-type super-VOA
assembled at the end of this file.  The state--field identification is
`mode_YBG_bgOmega_eq_Lbg`; the two polynomial operator comparisons remain separate reusable
lemmas, while `YBG_translation` supplies the genuinely field-valued VOA3 statement.

**(i) `mode (YBG bgOmega) (n+1) = BGVir.Lbg n`.**  This is the one that would deliver the
`virasoro` axiom outright, since `BGVir.Lbg_virasoro` already has exactly the shape
`SuperNearVOA.virasoro` demands, with `BGVir.centralCharge = -1`.

Write `s = -n-2`, so `mode (YBG ω) (n+1) = (YBG ω) s`.  By `YBG_bgOmega` and `nprod_apply`,

  `(YBG ω) s = ½ ∑ᶠ_m NO(βZ, ∂γZ)(m, s-m) - ½ ∑ᶠ_m NO(∂βZ, γZ)(m, s-m)`,

with `NO a b m t = if 0 ≤ m then a m ∘ b t else b t ∘ a m`.  Reindex each sum by the `β` **mode**
index `j` (recall `betaZ m = β₍₋ₘ₋₁₎ = BGVir.bM (-m-1)` and `gammaZ t = BGVir.gM (-t-1)`):

* first sum, `j = -m-1`: `0 ≤ m ⟺ j < 0`, matching `BGVir.bgOp`'s split exactly; the derivative
  contributes the scalar `s-m+1 = j-n` and the `γ` index becomes `n-j-1`.  Contribution
  `½ (j-n) · bgOp n j`.
* second sum, `j = -m-2`: the derivative contributes `m+1 = -j-1` and again `γ` index `n-j-1`.
  Its split is `0 ≤ m ⟺ j ≤ -2`, which differs from `BGVir.bgOp`'s `j < 0` **only at `j = -1`** —
  and there the scalar `m+1 = 0` kills the term, so the two orderings agree where it matters.
  Contribution `-½ (-j-1) · bgOp n j = ½ (j+1) · bgOp n j`.

Summing, the coefficient of `bgOp n j` is `½(j-n) + ½(j+1) = j + ½ - n/2`, which is *exactly*
`BGVir.Acoef n j`.  This is formalized by `mode_YBG_bgOmega_eq_Lbg`, using the two global
`finsum_comp_equiv` reindexings, the explicit `j = -1` vanishing, and `finsum_add_distrib` with
`BGVir.bgTerm_support_finite`.

**(ii) `L0_grading`.**  The auxiliary operator statement `BGVir.Lbg 0 = BGGrad.L0BG` is
proved by polynomial induction (`Lbg_zero_eq_L0BG`).  Together with the existing
`L0BG_eq_smul_of_mem` and (i), it supplies the grading axiom of `bgSNVOA`.

**(iii) `translation`.**  The auxiliary operator statement `BGVir.Lbg (-1) = BG.T` is proved
by polynomial induction (`Lbg_neg_one_eq_T`).  At `n=-1`, (i) identifies the conformal mode with
`T`; `YBG_translation` then proves `YBG (T v) = deriv (YBG v)` for all `v` by the
reconstruction-uniqueness/tower argument.  Thus `bgSNVOA` and its CFT-type upgrade `bgSVOA` are
unconditional, with half-integral weights and purely even parity kept independent.
-/

/-- The explicit Virasoro translation operator agrees with the polynomial translation
derivation.  This is one of the two operator identifications needed for the conformal upgrade;
it uses only the creation-mode commutators, so no reconstruction uniqueness is involved. -/
theorem Lbg_neg_one_eq_T : BGVir.Lbg (-1) = T := by
  apply LinearMap.ext
  intro p
  induction p using MvPolynomial.induction_on with
  | C a =>
      rw [show (MvPolynomial.C a : Fock) = a • (1 : Fock) by
        rw [smul_eq_C_mul, mul_one], map_smul, map_smul]
      have hL : BGVir.Lbg (-1) (1 : Fock) = 0 := by
        simpa only [BGVir.vacBG] using BGVir.Lbg_neg_one_vacuum
      rw [hL, T_one]
  | add p q hp hq => simp [map_add, hp, hq]
  | mul_X p i hp =>
      rcases i with k | k
      · rw [mul_comm p (X (Sum.inl k) : Fock)]
        change BGVir.Lbg (-1) (mulX (Sum.inl k) p) = T (mulX (Sum.inl k) p)
        have hT := DFunLike.congr_fun (T_mulX (Sum.inl k)) p
        change T (mulX (Sum.inl k) p) - mulX (Sum.inl k) (T p) = _ at hT
        rw [sub_eq_iff_eq_add] at hT
        simp only [LinearMap.smul_apply, lvl_inl, up_inl] at hT
        rw [BGVir.Lbg_neg_one_creation_inl, hT, hp]
        rw [add_comm]
      · rw [mul_comm p (X (Sum.inr k) : Fock)]
        change BGVir.Lbg (-1) (mulX (Sum.inr k) p) = T (mulX (Sum.inr k) p)
        have hT := DFunLike.congr_fun (T_mulX (Sum.inr k)) p
        change T (mulX (Sum.inr k) p) - mulX (Sum.inr k) (T p) = _ at hT
        rw [sub_eq_iff_eq_add] at hT
        simp only [LinearMap.smul_apply, lvl_inr, up_inr] at hT
        rw [BGVir.Lbg_neg_one_creation_inr, hT, hp]
        rw [add_comm]

/-- The explicit Virasoro zero mode is the Euler operator defining `gradingBG`.  Thus the
half-integral grading is genuinely the `L₀` eigenspace grading, rather than an auxiliary
grading on the same Fock space. -/
theorem Lbg_zero_eq_L0BG : BGVir.Lbg 0 = L0BG := by
  apply LinearMap.ext
  intro p
  induction p using MvPolynomial.induction_on with
  | C a =>
      rw [show (MvPolynomial.C a : Fock) = a • (1 : Fock) by
        rw [smul_eq_C_mul, mul_one], map_smul, map_smul]
      have hL : BGVir.Lbg 0 (1 : Fock) = 0 := by
        simpa only [BGVir.vacBG] using BGVir.Lbg_vacuum (by norm_num : (-1 : ℤ) ≤ 0)
      rw [hL, L0BG_one]
  | add p q hp hq => simp [map_add, hp, hq]
  | mul_X p i hp =>
      rcases i with k | k
      · rw [mul_comm p (X (Sum.inl k) : Fock)]
        change BGVir.Lbg 0 (mulX (Sum.inl k) p) = L0BG (mulX (Sum.inl k) p)
        have hL0 : L0BG (mulX (Sum.inl k) p) =
            mulX (Sum.inl k) (L0BG p) + bgWt (Sum.inl k) • mulX (Sum.inl k) p := by
          rw [mulX_apply, L0BG_mul, L0BG_X]
          rw [mul_smul_comm, mul_comm p]
          rfl
        have hwt : BGVir.wtBG 0 (-(k : ℤ) - 1) = (k : ℂ) + 1 / 2 := by
          simp only [BGVir.wtBG]
          push_cast
          ring
        rw [← BGVir.bM_neg_eq_mulX, BGVir.Lbg_bM_apply, hp, BGVir.bM_neg_eq_mulX,
          hwt, show (0 : ℤ) + (-(k : ℤ) - 1) = -(k : ℤ) - 1 by ring,
          BGVir.bM_neg_eq_mulX, hL0, bgWt_inl]
      · rw [mul_comm p (X (Sum.inr k) : Fock)]
        change BGVir.Lbg 0 (mulX (Sum.inr k) p) = L0BG (mulX (Sum.inr k) p)
        have hL0 : L0BG (mulX (Sum.inr k) p) =
            mulX (Sum.inr k) (L0BG p) + bgWt (Sum.inr k) • mulX (Sum.inr k) p := by
          rw [mulX_apply, L0BG_mul, L0BG_X]
          rw [mul_smul_comm, mul_comm p]
          rfl
        have hwt : BGVir.wtBG 0 (-(k : ℤ) - 1) = (k : ℂ) + 1 / 2 := by
          simp only [BGVir.wtBG]
          push_cast
          ring
        rw [← BGVir.gM_neg_eq_mulX, BGVir.Lbg_gM_apply, hp, BGVir.gM_neg_eq_mulX,
          hwt, show (0 : ℤ) + (-(k : ℤ) - 1) = -(k : ℤ) - 1 by ring,
          BGVir.gM_neg_eq_mulX, hL0, bgWt_inr]

/-- The remaining state--field comparison, expanded to the two locally finite normal-ordering
sums.  This deliberately stops before reindexing: the next lemmas may treat the two affine
changes of summation variable independently, with their own finite-support witnesses. -/
theorem mode_YBG_bgOmega_expanded (n : ℤ) (x : Fock) :
    mode (YBG bgOmega) (n + 1) x =
      (1 / 2 : ℂ) • ∑ᶠ m : ℤ,
          normalOrdered betaZ (VOA.deriv gammaZ) m (-n - 2 - m) x
        - (1 / 2 : ℂ) • ∑ᶠ m : ℤ,
          normalOrdered (VOA.deriv betaZ) gammaZ m (-n - 2 - m) x := by
  rw [mode_apply, YBG_bgOmega_fields]
  change ((1 / 2 : ℂ) • (nprod betaZ_isField gammaZ_isField.deriv) (-(n + 1) - 1)
      - (1 / 2 : ℂ) • (nprod betaZ_isField.deriv gammaZ_isField) (-(n + 1) - 1)) x = _
  simp only [LinearMap.sub_apply, LinearMap.smul_apply]
  rw [nprod_apply betaZ_isField gammaZ_isField.deriv,
    nprod_apply betaZ_isField.deriv gammaZ_isField]
  congr 2 <;> ring

/-- Pointwise reindexing of the `:β\,∂γ:` summand.  The inequality controlling ordinary
normal ordering is transported exactly to the inequality in `BGVir.bgOp`; no parity sign occurs. -/
theorem normalOrdered_beta_deriv_gamma_reindex (n j : ℤ) :
    normalOrdered betaZ (VOA.deriv gammaZ) (-j - 1) (-n - 2 - (-j - 1))
      = ((j : ℂ) - n) • BGVir.bgOp n j := by
  apply LinearMap.ext
  intro x
  rw [normalOrdered_apply, deriv_apply, betaZ_eq, gammaZ_eq]
  simp only [LinearMap.smul_apply, BGVir.bgOp_apply, BGVir.bM, BGVir.gM]
  by_cases hj : j < 0
  · have hm : 0 ≤ -j - 1 := by omega
    rw [if_pos hm, if_pos hj]
    rw [show -n - 2 - (-j - 1) + 1 = j - n by ring,
      show -(-j - 1) - 1 = j by ring,
      show -(j - n) - 1 = n - j - 1 by ring, Module.End.mul_apply]
    rw [← Int.cast_smul_eq_zsmul ℂ (j - n), LinearMap.smul_apply, map_smul]
    push_cast
    rfl
  · have hm : ¬ 0 ≤ -j - 1 := by omega
    rw [if_neg hm, if_neg hj]
    rw [show -n - 2 - (-j - 1) + 1 = j - n by ring,
      show -(-j - 1) - 1 = j by ring,
      show -(j - n) - 1 = n - j - 1 by ring, Module.End.mul_apply]
    rw [← Int.cast_smul_eq_zsmul ℂ (j - n) (gamma (n - j - 1)), LinearMap.smul_apply]
    push_cast
    ring

/-- Pointwise reindexing of the `:∂β\,γ:` summand.  The exceptional index `j = -1` is
explicit: the two normal-ordering conventions differ there, but the derivative coefficient is
zero, so the correction vanishes. -/
theorem normalOrdered_deriv_beta_gamma_reindex (n j : ℤ) :
    normalOrdered (VOA.deriv betaZ) gammaZ (-j - 2) (-n - 2 - (-j - 2))
      = (-(j : ℂ) - 1) • BGVir.bgOp n j := by
  apply LinearMap.ext
  intro x
  rw [normalOrdered_apply, deriv_apply, betaZ_eq, gammaZ_eq]
  simp only [LinearMap.smul_apply, BGVir.bgOp_apply, BGVir.bM, BGVir.gM]
  by_cases hminus : j = -1
  · subst j
    norm_num
  by_cases hj : j < 0
  · have hm : 0 ≤ -j - 2 := by omega
    rw [if_pos hm, if_pos hj]
    rw [show -j - 2 + 1 = -j - 1 by ring,
      show -(-j - 1) - 1 = j by ring,
      show -n - 2 - (-j - 2) = j - n by ring,
      show -(j - n) - 1 = n - j - 1 by ring, Module.End.mul_apply]
    rw [← Int.cast_smul_eq_zsmul ℂ (-j - 1) (beta j), LinearMap.smul_apply]
    congr 1
    push_cast
    ring
  · have hm : ¬ 0 ≤ -j - 2 := by omega
    rw [if_neg hm, if_neg hj]
    rw [show -j - 2 + 1 = -j - 1 by ring,
      show -(-j - 1) - 1 = j by ring,
      show -n - 2 - (-j - 2) = j - n by ring,
      show -(j - n) - 1 = n - j - 1 by ring, Module.End.mul_apply]
    rw [← Int.cast_smul_eq_zsmul ℂ (-j - 1) (beta j), LinearMap.smul_apply, map_smul]
    push_cast
    ring

/-- The two affine involutions needed to compare the normal-ordered field coefficients with
the Virasoro summation convention. -/
def betaDerivGammaEquiv : ℤ ≃ ℤ where
  toFun j := -j - 1
  invFun m := -m - 1
  left_inv _ := by dsimp; ring
  right_inv _ := by dsimp; ring

def derivBetaGammaEquiv : ℤ ≃ ℤ where
  toFun j := -j - 2
  invFun m := -m - 2
  left_inv _ := by dsimp; ring
  right_inv _ := by dsimp; ring

@[simp] theorem betaDerivGammaEquiv_apply (j : ℤ) : betaDerivGammaEquiv j = -j - 1 := rfl
@[simp] theorem derivBetaGammaEquiv_apply (j : ℤ) : derivBetaGammaEquiv j = -j - 2 := rfl

/-- The first normal-ordering coefficient, globally reindexed from the field exponent to the
`BGVir` mode index. -/
theorem finsum_beta_deriv_gamma_reindex (n : ℤ) (x : Fock) :
    (∑ᶠ m : ℤ, normalOrdered betaZ (VOA.deriv gammaZ) m (-n - 2 - m) x)
      = ∑ᶠ j : ℤ, (((j : ℂ) - n) • BGVir.bgOp n j) x := by
  rw [← finsum_comp_equiv betaDerivGammaEquiv]
  apply finsum_congr
  intro j
  have h : normalOrdered betaZ (deriv gammaZ) (-j - 1) (-n - 2 - (-j - 1)) =
      ((j : ℂ) - n) • BGVir.bgOp n j :=
    normalOrdered_beta_deriv_gamma_reindex n j
  simpa only [betaDerivGammaEquiv, LinearMap.smul_apply] using LinearMap.congr_fun h x

/-- The second normal-ordering coefficient, globally reindexed from the field exponent to the
`BGVir` mode index.  The pointwise lemma has already absorbed the exceptional `j=-1` term. -/
theorem finsum_deriv_beta_gamma_reindex (n : ℤ) (x : Fock) :
    (∑ᶠ m : ℤ, normalOrdered (VOA.deriv betaZ) gammaZ m (-n - 2 - m) x)
      = ∑ᶠ j : ℤ, (-(j : ℂ) - 1) • BGVir.bgOp n j x := by
  rw [← finsum_comp_equiv derivBetaGammaEquiv]
  apply finsum_congr
  intro j
  have h : normalOrdered (deriv betaZ) gammaZ (-j - 2) (-n - 2 - (-j - 2)) =
      (-(j : ℂ) - 1) • BGVir.bgOp n j :=
    normalOrdered_deriv_beta_gamma_reindex n j
  simpa only [derivBetaGammaEquiv, LinearMap.smul_apply] using LinearMap.congr_fun h x

/-- The reconstructed conformal field has exactly the finite-sum Virasoro modes.  This is an
ordinary (purely even) normal-ordering calculation: the two affine reindexings above account
for every coefficient, including the zero correction at `j = -1`. -/
theorem mode_YBG_bgOmega_eq_Lbg (n : ℤ) :
    mode (YBG bgOmega) (n + 1) = BGVir.Lbg n := by
  apply LinearMap.ext
  intro x
  rw [mode_YBG_bgOmega_expanded, finsum_beta_deriv_gamma_reindex,
    finsum_deriv_beta_gamma_reindex]
  simp only [LinearMap.smul_apply]
  have hfin₁ := BGVir.bgTerm_support_finite (fun j : ℤ => (j : ℂ) - n) n x
  have hfin₂ := BGVir.bgTerm_support_finite (fun j : ℤ => -(j : ℂ) - 1) n x
  rw [smul_finsum' (1 / 2 : ℂ) hfin₁, smul_finsum' (1 / 2 : ℂ) hfin₂]
  have hfin₁' : (Function.support fun j : ℤ =>
      (1 / 2 : ℂ) • (((j : ℂ) - n) • BGVir.bgOp n j x)).Finite := by
    apply hfin₁.subset
    intro j hj
    rw [Function.mem_support] at hj ⊢
    intro hz
    exact hj (by rw [hz, smul_zero])
  have hfin₂' : (Function.support fun j : ℤ =>
      (1 / 2 : ℂ) • ((-(j : ℂ) - 1) • BGVir.bgOp n j x)).Finite := by
    apply hfin₂.subset
    intro j hj
    rw [Function.mem_support] at hj ⊢
    intro hz
    exact hj (by rw [hz, smul_zero])
  rw [← finsum_sub_distrib hfin₁' hfin₂', BGVir.Lbg_apply]
  apply finsum_congr
  intro j
  simp only [smul_smul, BGVir.Acoef]
  rw [← sub_smul]
  congr 1
  ring

/-- The first nonconstant rung of the reconstructed vacuum tower. -/
theorem YBG_one_vac (u : Fock) : (YBG u) 1 vac = T u := by
  have h := congrArg (fun (R : Module.End ℂ Fock) => R vac) (YBG_DCovariant u 0)
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
  rw [T_vac, map_zero, sub_zero, YBG_creation, show ((0 : ℤ) + 1) = 1 by ring,
    one_smul] at h
  exact h.symm

/-- The derivative of a reconstructed field still has no negative vacuum coefficients. -/
theorem deriv_YBG_vacuum_neg (u : Fock) {q : ℤ} (hq : q < 0) :
    (VOA.deriv (YBG u)) q vac = 0 := by
  rw [deriv_apply]
  change ((q + 1 : ℤ) • (YBG u) (q + 1)) vac = 0
  rw [← Int.cast_smul_eq_zsmul ℂ (q + 1), LinearMap.smul_apply]
  by_cases hq1 : q + 1 < 0
  · rw [YBG_creation_neg u hq1, smul_zero]
  · rw [show q + 1 = (0 : ℤ) from by omega, Int.cast_zero, zero_smul]

/-- `Y(Tv,z)` and `∂_zY(v,z)` have the same vacuum base. -/
theorem YBG_translation_base (u : Fock) :
    (YBG (T u)) 0 vac = (VOA.deriv (YBG u)) 0 vac := by
  rw [YBG_creation, deriv_apply]
  change T u = ((0 + 1 : ℤ) • (YBG u) (0 + 1)) vac
  rw [← Int.cast_smul_eq_zsmul ℂ (0 + 1), LinearMap.smul_apply,
    show (0 + 1 : ℤ) = 1 by ring, Int.cast_one, one_smul, YBG_one_vac]

/-- VOA3 on a creation word, by the reconstruction uniqueness theorem.  All locality signs are
`+1`, because the beta--gamma carrier is purely even; this does not invoke spin--statistics. -/
theorem YBG_translation_word (l₀ : BGWord) :
    YBG (T (stWordBG l₀)) = VOA.deriv (YBG (stWordBG l₀)) := by
  have hAvac : ∀ q : ℤ,
      (YBG (T (stWordBG l₀)) - VOA.deriv (YBG (stWordBG l₀))) q vac = 0 := by
    intro q
    change ((YBG (T (stWordBG l₀))) q - (VOA.deriv (YBG (stWordBG l₀))) q) vac = 0
    rw [LinearMap.sub_apply, sub_eq_zero]
    exact tower_unique (YBG_DCovariant (T (stWordBG l₀)))
      (DCovariant.deriv' (YBG_DCovariant (stWordBG l₀))) T_vac
      (YBG_translation_base (stWordBG l₀))
      (fun q hq => YBG_creation_neg (T (stWordBG l₀)) hq)
      (fun q hq => deriv_YBG_vacuum_neg (stWordBG l₀) hq) q
  have hloc : ∀ l : BGWord,
      Localε 1 (YBG (T (stWordBG l₀)) - VOA.deriv (YBG (stWordBG l₀))) (YwordBG l) := by
    intro l
    have h1 : Localε 1 (YBG (T (stWordBG l₀))) (YwordBG l) := by
      rw [localε_one_iff, ← YBG_word]
      exact YBG_local _ _
    have h2 : Localε 1 (VOA.deriv (YBG (stWordBG l₀))) (YwordBG l) := by
      rw [localε_one_iff, ← YBG_word]
      exact (YBG_local _ _).derivL
    rw [sub_eq_add_neg, ← neg_one_smul ℂ (VOA.deriv (YBG (stWordBG l₀)))]
    exact Localε.add_left h1 (Localε.smul_left _ (-1) h2)
  have hz := field_eq_zero_of_vacuumε (fun _ : BGWord => 1) vac
    (YBG (T (stWordBG l₀)) - VOA.deriv (YBG (stWordBG l₀))) stWordBG YwordBG
    hloc YwordBG_vacuum_base (fun l _q hq => YwordBG_vacuum_neg l hq) hAvac stWordBG_span
  rwa [sub_eq_zero] at hz

/-- VOA3 for every beta--gamma state. -/
theorem YBG_translation (u : Fock) : YBG (T u) = VOA.deriv (YBG u) := by
  have h : YBG.comp T =
      (VOA.deriv : FormalDist (Module.End ℂ Fock) →ₗ[ℂ]
        FormalDist (Module.End ℂ Fock)).comp YBG := by
    refine LinearMap.ext_on stWordBG_span ?_
    rintro _ ⟨l, rfl⟩
    exact YBG_translation_word l
  exact congrArg (fun (F : Fock →ₗ[ℂ] FormalDist (Module.End ℂ Fock)) => F u) h

/-- The half-integral beta--gamma grading is bounded below by zero. -/
theorem gradingBG_eq_bot_of_re_neg {h : ℂ} (hh : h.re < 0) : gradingBG h = ⊥ := by
  apply gradingBG_eq_bot_of_not_two_mul_nat
  intro n hn
  have hre := congrArg Complex.re hn
  norm_num [Complex.mul_re] at hre
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith

/-- The beta--gamma conformal structure before imposing CFT type.  Its Virasoro modes are the
explicit finite sums `BGVir.Lbg`; the conformal vector is even for the independent reason that
the entire carrier is purely even. -/
noncomputable def bgSNVOA : SuperNearVOA Fock where
  __ := bgSVA
  conformalVector := bgOmega
  conformal_mem := bgOmega_mem_grading_two
  conformal_parity := bgOmega_mem_parity_zero
  centralCharge := BGVir.centralCharge
  virasoro := by
    intro m n
    change ⁅mode (YBG bgOmega) (m + 1), mode (YBG bgOmega) (n + 1)⁆ =
      ((m : ℂ) - n) • mode (YBG bgOmega) (m + n + 1)
        + (if m + n = 0 then (((m : ℂ) ^ 3 - m) / 12 * BGVir.centralCharge) •
          (1 : Module.End ℂ Fock) else 0)
    rw [mode_YBG_bgOmega_eq_Lbg m, mode_YBG_bgOmega_eq_Lbg n,
      mode_YBG_bgOmega_eq_Lbg (m + n)]
    rw [LieRing.of_associative_ring_bracket]
    by_cases hmn : m + n = 0
    · rw [if_pos hmn]
      simpa [hmn] using BGVir.Lbg_virasoro m n
    · rw [if_neg hmn]
      simpa [hmn] using BGVir.Lbg_virasoro m n
  L0_grading := by
    intro h v hv
    change mode (YBG bgOmega) 1 v = h • v
    rw [show (1 : ℤ) = 0 + 1 by ring, mode_YBG_bgOmega_eq_Lbg 0, Lbg_zero_eq_L0BG]
    exact L0BG_eq_smul_of_mem hv
  translation := by
    intro v
    change YBG (mode (YBG bgOmega) 0 v) = VOA.deriv (YBG v)
    rw [show (0 : ℤ) = -1 + 1 by ring, mode_YBG_bgOmega_eq_Lbg (-1), Lbg_neg_one_eq_T]
    exact YBG_translation v

/-- The beta--gamma system is a CFT-type super VOA, with half-integral weights but trivial
parity.  This is deliberately not a spin-statistics assertion. -/
noncomputable def bgSVOA : SuperVertexOperatorAlgebra Fock :=
  bgSNVOA.toSVOA (by simpa only using gradingBG_zero) (fun h hh => gradingBG_eq_bot_of_re_neg hh)

end VOA.BGInst
