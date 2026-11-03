/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Examples.SymplecticFermionInstance
import VOA.Examples.SymplecticFermionVirasoroA
import VOA.Core.SuperNearVOA

/-!
# Symplectic fermions: the **super vertex operator algebra**

`sympFermSVOA : SuperVertexOperatorAlgebra FockSF` — the first `SuperVertexOperatorAlgebra` in
the library, with central charge `c = -2`.

`Examples.SymplecticFermionInstance` produced the `SuperVertexAlgebra`, and
`Examples.SymplecticFermionVirasoroA` produced the whole conformal layer: `ωSF`, the Virasoro
relation at `c = -2` (`YSF_omega_virasoro`), `L₀` acting by the weight (`LSF_zero_grading`), and
`L₋₁ = T` (`LSF_neg_one_eq_T`).  What is missing, and what this file supplies, is

* **VOA3 (translation) in the `Y`-form** `Y(L₋₁v, z) = ∂_z Y(v,z)` — the operator identity
  `L₋₁ = T` is *not* the same statement as the field identity, and getting from one to the other
  needs the super Goddard uniqueness argument (§3 below);
* **VOA4, the two CFT-type conditions** — `𝒱₀ = ℂ|0⟩` and "no weights of negative real part"
  (§1), both of which are pure word combinatorics here;
* the assembly of `SuperNearVOA` (§4) and the upgrade to `SuperVertexOperatorAlgebra` (§5).

## §1 in one line

`sfWeight l = ∑ᵢ (kᵢ + 1)`, a sum of **positive** integers, so it is `0` exactly for the empty
word and never negative.  Hence `gradingSF 0` is spanned by `stWordSF [] = |0⟩`, and
`gradingSF h = ⊥` whenever `h` is not a natural number — in particular whenever `Re h < 0`.
Note that this is much stronger than positivity: symplectic fermions have *no* non-integral
weights at all, in either parity.

## §3: why translation is real work

`reconstructε` hands back `DCovariant T (YSF u)`, i.e. `[T, u₍ₘ₎] = (m+1)u₍ₘ₊₁₎`, which is
`[T, Y(u,z)] = ∂_z Y(u,z)`.  VOA3 asks instead for `Y(Tu, z) = ∂_z Y(u,z)` — a statement about a
*different state*, not a commutator.  The standard bridge is operator-first uniqueness: the two
fields `Y(Tu,z)` and `∂_z Y(u,z)`

1. are both `T`-covariant, kill the vacuum in negative degree, and have the same `z⁰` action on
   the vacuum (`YSF_one_vac`: `u₍₁₎|0⟩ = Tu`), hence have the *same whole vacuum tower*
   (`tower_unique`);
2. are both `ε`-local with every word field.

`field_eq_zero_of_vacuumε` then says their difference is zero.  This is the bosonic
`Examples/AffineSl2Assembly.YA_translation` argument, transplanted to the Koszul-signed setting;
the only genuinely new ingredient is that locality is available **only for
parity-homogeneous states**, so the argument is run on a single word `stWordSF l₀` (which *is*
parity-homogeneous, of parity `|l₀|`) and extended to all of `FockSF` by linearity at the end.

For that to work `T` must preserve the parity — which it does, because `T = ω₍₀₎` and `ω` is
even (`T_mem_evenOdd`, via `YSF_ParField`).  This is not spin–statistics: it is only the
statement that an even operator preserves the parity decomposition.
-/

namespace VOA.SympFerm

open VOA
open CliffordAlgebra
open Module (End)
open VOA.Reconstruction

/-! ## §1  The two CFT-type conditions (VOA4)

Both are statements about `sfWeight`, which is a sum of the strictly positive numbers `kᵢ + 1`. -/

/-- A word of weight `0` is the empty word: every letter contributes at least `1`. -/
theorem eq_nil_of_sfWeight_eq_zero {l : SFWord} (h : sfWeight l = 0) : l = [] := by
  cases l with
  | nil => rfl
  | cons p rest =>
      rw [sfWeight_cons] at h
      omega

/-- The words of weight `0` are exactly the empty word. -/
theorem sfWordsAt_zero : sfWordsAt (0 : ℂ) = {([] : SFWord)} := by
  ext l
  constructor
  · intro hl
    have hc : ((sfWeight l : ℕ) : ℂ) = 0 := hl
    have h0 : sfWeight l = 0 := by exact_mod_cast hc
    exact eq_nil_of_sfWeight_eq_zero h0
  · intro hl
    have hnil : l = ([] : SFWord) := hl
    subst hnil
    change ((sfWeight ([] : SFWord) : ℕ) : ℂ) = 0
    rw [sfWeight_nil, Nat.cast_zero]

/-- **VOA4, part 1 (`vacuum_grade`): `𝒱₀ = ℂ|0⟩`.**  The weight-`0` piece is by definition the
span of the weight-`0` word states, and there is exactly one weight-`0` word — the empty one,
whose state is the vacuum. -/
theorem gradingSF_zero : gradingSF 0 = (ℂ ∙ vacSF) := by
  rw [gradingSF, sfWordsAt_zero, Set.image_singleton, stWordSF_nil]

/-- No word has a weight of negative real part: word weights are natural numbers. -/
theorem sfWordsAt_eq_empty_of_re_neg {h : ℂ} (hh : h.re < 0) : sfWordsAt h = ∅ := by
  ext l
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hl
  have hc : ((sfWeight l : ℕ) : ℂ) = h := hl
  have hre : h.re = ((sfWeight l : ℕ) : ℝ) := by rw [← hc]; simp
  rw [hre] at hh
  exact absurd hh (not_lt.mpr (Nat.cast_nonneg _))

/-- **VOA4, part 2 (`positivity`): no conformal weights of negative real part.** -/
theorem gradingSF_eq_bot_of_re_neg (h : ℂ) (hh : h.re < 0) : gradingSF h = ⊥ := by
  rw [gradingSF, sfWordsAt_eq_empty_of_re_neg hh, Set.image_empty, Submodule.span_empty]

/-! ## §2  The conformal vector is even

`ωSF = -χ⁰₋₁χ¹₋₁|0⟩` is a two-letter word, hence of parity `2 mod 2 = 0`.  This is the
`conformal_parity` field, and — via `parity_mode` — the reason `T = ω₍₀₎` preserves the parity. -/

/-- **`ωSF` is even.**  A genuine axiom of `SuperNearVOA`, discharged here by the length of the
word: `ωSF` is (minus) a product of *two* odd generators. -/
theorem omega_mem_evenOdd : ωSF ∈ evenOdd QSF 0 := by
  have h := stWordSF_mem_evenOdd [((0 : ℕ), (0 : Fin 2)), ((0 : ℕ), (1 : Fin 2))]
  rw [show ((([((0 : ℕ), (0 : Fin 2)), ((0 : ℕ), (1 : Fin 2))] : SFWord).length : ℕ) : ZMod 2)
      = 0 from by decide] at h
  exact Submodule.neg_mem _ h

/-! ## §3  VOA3: the translation property `Y(Tv, z) = ∂_z Y(v, z)` -/

/-- `ω₍₀₎ = T`: the mode the `SuperNearVOA.translation` field speaks about is the translation
operator `reconstructε` was fed.  This is `LSF_neg_one_eq_T` in mode notation. -/
theorem mode_YSF_omega_zero : mode (YSF ωSF) 0 = T := by
  have h := LSF_eq_mode (-1)
  rw [LSF_neg_one_eq_T, show (-1 : ℤ) + 1 = 0 from by ring] at h
  exact h.symm

/-- `ω₍₁₎ = L₀`, likewise: the mode the `L0_grading` field speaks about. -/
theorem mode_YSF_omega_one : mode (YSF ωSF) 1 = LSF 0 := by
  have h := LSF_eq_mode 0
  rw [show (0 : ℤ) + 1 = 1 from by ring] at h
  exact h.symm

/-- The `z⁻¹`-coefficient of `Y(ω, z)` is `T`. -/
theorem YSF_omega_neg_one : (YSF ωSF) (-1) = T := by
  rw [← mode_YSF_omega_zero, mode_apply, show -(0 : ℤ) - 1 = -1 from by ring]

/-- **`T` preserves the parity.**  `T = ω₍₀₎` and `ω` is even, so this is `parity_mode` for the
conformal vector — no spin–statistics involved. -/
theorem T_mem_evenOdd {r : ZMod 2} {x : FockSF} (hx : x ∈ evenOdd QSF r) :
    T x ∈ evenOdd QSF r := by
  have h := YSF_ParField omega_mem_evenOdd (-1) r x hx
  rw [zero_add, YSF_omega_neg_one] at h
  exact h

/-- **Locality of `YSF u` against a single word field**, for `u` of definite parity.

`YSF_localε` is phrased for two states presented as parity-homogeneous `Finsupp` combinations of
words; the right-hand state here is a single word, fed in as `Finsupp.single l 1`. -/
theorem YSF_localε_word {p : ZMod 2} {u : FockSF} (hu : u ∈ evenOdd QSF p) (l : SFWord) :
    Localε (koszul p ((l.length : ℕ) : ZMod 2)) (YSF u) (YwordSF l) := by
  classical
  rw [evenOdd_eq_parityPieceSF, parityPieceSF] at hu
  obtain ⟨c, hcs, rfl⟩ := (Finsupp.mem_span_image_iff_linearCombination ℂ).mp hu
  have hc : ∀ i ∈ c.support, ((i.length : ℕ) : ZMod 2) = p := fun i hi =>
    (Finsupp.mem_supported ℂ c).mp hcs (Finset.mem_coe.mpr hi)
  have hd : ∀ j ∈ (Finsupp.single l (1 : ℂ)).support,
      ((j.length : ℕ) : ZMod 2) = ((l.length : ℕ) : ZMod 2) := by
    intro j hj
    rw [Finsupp.support_single l (one_ne_zero), Finset.mem_singleton] at hj
    rw [hj]
  have h := YSF_localε p ((l.length : ℕ) : ZMod 2) c (Finsupp.single l (1 : ℂ)) hc hd
  rwa [Finsupp.linearCombination_single, one_smul, YSF_word] at h

/-- **The first rung of the creation tower**: `u₍₁₎|0⟩ = Tu`.  Translation covariance at `m = 0`,
evaluated on the vacuum, using `T|0⟩ = 0` and `u₍₀₎|0⟩ = u`. -/
theorem YSF_one_vac (u : FockSF) : (YSF u) 1 vacSF = T u := by
  have h := congrArg (fun (R : End ℂ FockSF) => R vacSF) (YSF_DCovariant u 0)
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply] at h
  rw [T_one, map_zero, sub_zero, YSF_creation, show ((0 : ℤ) + 1) = 1 from by ring,
    one_smul] at h
  exact h.symm

/-- `∂_z Y(v,z)` also has no pole on the vacuum. -/
theorem deriv_YSF_vacuum_neg (v : FockSF) {q : ℤ} (hq : q < 0) :
    (VOA.deriv (YSF v)) q vacSF = 0 := by
  rw [deriv_apply]
  change ((q + 1 : ℤ) • (YSF v) (q + 1)) vacSF = 0
  rw [← Int.cast_smul_eq_zsmul ℂ (q + 1), LinearMap.smul_apply]
  by_cases hq1 : q + 1 < 0
  · rw [YSF_creation_neg v hq1, smul_zero]
  · rw [show q + 1 = (0 : ℤ) from by omega, Int.cast_zero, zero_smul]

/-- `Y(Tv,z)` and `∂_z Y(v,z)` create the same state from the vacuum. -/
theorem YSF_translation_base (v : FockSF) :
    (YSF (T v)) 0 vacSF = (VOA.deriv (YSF v)) 0 vacSF := by
  rw [YSF_creation, deriv_apply]
  change T v = ((0 + 1 : ℤ) • (YSF v) (0 + 1)) vacSF
  rw [← Int.cast_smul_eq_zsmul ℂ (0 + 1), LinearMap.smul_apply,
    show (0 + 1 : ℤ) = 1 from by ring, Int.cast_one, one_smul, YSF_one_vac]

/-- **VOA3 on a word.**  `Y(T·stWordSF l₀, z) = ∂_z Y(stWordSF l₀, z)`.

The two fields have the same vacuum tower (`tower_unique`, fed by `YSF_translation_base` and the
two vacuum-annihilation facts) and are both `ε`-local with every word field at the *same* sign
`koszul |l₀| |l|` — for the left-hand one because `T` preserves the parity.  Super Goddard
uniqueness then kills their difference. -/
theorem YSF_translation_word (l₀ : SFWord) :
    YSF (T (stWordSF l₀)) = VOA.deriv (YSF (stWordSF l₀)) := by
  have hTmem : T (stWordSF l₀) ∈ evenOdd QSF ((l₀.length : ℕ) : ZMod 2) :=
    T_mem_evenOdd (stWordSF_mem_evenOdd l₀)
  have hAvac : ∀ q : ℤ,
      (YSF (T (stWordSF l₀)) - VOA.deriv (YSF (stWordSF l₀))) q vacSF = 0 := by
    intro q
    change ((YSF (T (stWordSF l₀))) q - (VOA.deriv (YSF (stWordSF l₀))) q) vacSF = 0
    rw [LinearMap.sub_apply, sub_eq_zero]
    exact tower_unique (YSF_DCovariant (T (stWordSF l₀)))
      (DCovariant.deriv' (YSF_DCovariant (stWordSF l₀))) T_one
      (YSF_translation_base (stWordSF l₀))
      (fun q hq => YSF_creation_neg (T (stWordSF l₀)) hq)
      (fun q hq => deriv_YSF_vacuum_neg (stWordSF l₀) hq) q
  have hloc : ∀ l : SFWord,
      Localε (koszul ((l₀.length : ℕ) : ZMod 2) ((l.length : ℕ) : ZMod 2))
        (YSF (T (stWordSF l₀)) - VOA.deriv (YSF (stWordSF l₀))) (YwordSF l) := by
    intro l
    have h1 := YSF_localε_word hTmem l
    have h2 := (YSF_localε_word (stWordSF_mem_evenOdd l₀) l).derivL
    rw [sub_eq_add_neg, ← neg_one_smul ℂ (VOA.deriv (YSF (stWordSF l₀)))]
    exact Localε.add_left h1 (Localε.smul_left _ (-1) h2)
  have hz := field_eq_zero_of_vacuumε
    (fun l : SFWord => koszul ((l₀.length : ℕ) : ZMod 2) ((l.length : ℕ) : ZMod 2)) vacSF
    (YSF (T (stWordSF l₀)) - VOA.deriv (YSF (stWordSF l₀))) stWordSF YwordSF
    hloc YwordSF_vacuum_base (fun l _q hq => YwordSF_vacuum_neg l hq) hAvac stWordSF_span
  rwa [sub_eq_zero] at hz

/-- **VOA3 (translation) for symplectic fermions**: `Y(Tv, z) = ∂_z Y(v, z)` for *every*
state `v`.  Both sides are `ℂ`-linear in `v` and the words span (`stWordSF_span`), so
`YSF_translation_word` suffices. -/
theorem YSF_translation (v : FockSF) : YSF (T v) = VOA.deriv (YSF v) := by
  have h : YSF.comp T
      = (VOA.deriv : FormalDist (End ℂ FockSF) →ₗ[ℂ] FormalDist (End ℂ FockSF)).comp
          YSF := by
    refine LinearMap.ext_on stWordSF_span ?_
    rintro _ ⟨l, rfl⟩
    exact YSF_translation_word l
  exact congrArg (fun (F : FockSF →ₗ[ℂ] FormalDist (End ℂ FockSF)) => F v) h

/-! ## §4  The super near-VOA

Everything above VOA4.  Stated as a `SuperNearVOA` first, because that is the structure the
even-part / orbifold machinery downstream consumes; the CFT-type upgrade is §5. -/

/-- **The symplectic-fermion super near-VOA**: the `SuperVertexAlgebra` of
`Examples.SymplecticFermionInstance` together with its full conformal layer — conformal vector
`ωSF`, central charge `c = -2`, VOA1 (`YSF_omega_virasoro`), VOA2 (`LSF_zero_grading`), VOA3
(`YSF_translation`). -/
noncomputable def sympFermSNVOA : SuperNearVOA FockSF where
  __ := sympFermSVA
  conformalVector := ωSF
  conformal_mem := omega_mem_grading
  conformal_parity := omega_mem_evenOdd
  centralCharge := sfCentralCharge
  virasoro := YSF_omega_virasoro
  L0_grading := by
    intro h v hv
    change mode (YSF ωSF) 1 v = h • v
    rw [mode_YSF_omega_one]
    exact LSF_zero_grading hv
  translation := by
    intro v
    change YSF (mode (YSF ωSF) 0 v) = VOA.deriv (YSF v)
    rw [mode_YSF_omega_zero]
    exact YSF_translation v

@[simp] theorem sympFermSNVOA_grading : sympFermSNVOA.grading = gradingSF := rfl

@[simp] theorem sympFermSNVOA_parity : sympFermSNVOA.parity = evenOdd QSF := rfl

@[simp] theorem sympFermSNVOA_Y : sympFermSNVOA.Y = YSF := rfl

@[simp] theorem sympFermSNVOA_vacuum : sympFermSNVOA.vacuum = vacSF := rfl

@[simp] theorem sympFermSNVOA_conformalVector : sympFermSNVOA.conformalVector = ωSF := rfl

@[simp] theorem sympFermSNVOA_centralCharge : sympFermSNVOA.centralCharge = -2 := rfl

/-- The Virasoro modes of the near-VOA are the `LSF n` built by hand. -/
theorem sympFermSNVOA_L (n : ℤ) : sympFermSNVOA.L n = LSF n := (LSF_eq_mode n).symm

/-- **VOA4, part 1, in structure form.** -/
theorem sympFermSNVOA_vacuum_grade :
    sympFermSNVOA.grading 0 = (ℂ ∙ sympFermSNVOA.vacuum) := gradingSF_zero

/-- **VOA4, part 2, in structure form.** -/
theorem sympFermSNVOA_positivity :
    ∀ h : ℂ, h.re < 0 → sympFermSNVOA.grading h = ⊥ := gradingSF_eq_bot_of_re_neg

/-- **Symplectic fermions are bounded below** — with the sharp bound `B = 0`, since the
weights are natural numbers.  (Unlike the doublet's ambient algebra, whose weights go negative,
this example satisfies the strong form.) -/
theorem sympFermSNVOA_boundedBelow : sympFermSNVOA.BoundedBelow :=
  sympFermSNVOA.boundedBelow_of_positivity sympFermSNVOA_positivity

/-! ## §5  The super vertex operator algebra -/

/-- **The symplectic-fermion super vertex operator algebra**, central charge `c = -2`.

The library's first `SuperVertexOperatorAlgebra`, and the first structure anywhere in it that
uses both generalization axes at once: a `ZMod 2` parity entering locality through the Koszul
sign, and odd fields of *integer* conformal weight (so `SpinStatistics` genuinely fails). -/
noncomputable def sympFermSVOA : SuperVertexOperatorAlgebra FockSF :=
  sympFermSNVOA.toSVOA sympFermSNVOA_vacuum_grade sympFermSNVOA_positivity

@[simp] theorem sympFermSVOA_grading : sympFermSVOA.grading = gradingSF := rfl

@[simp] theorem sympFermSVOA_parity : sympFermSVOA.parity = evenOdd QSF := rfl

@[simp] theorem sympFermSVOA_Y : sympFermSVOA.Y = YSF := rfl

@[simp] theorem sympFermSVOA_vacuum : sympFermSVOA.vacuum = vacSF := rfl

@[simp] theorem sympFermSVOA_conformalVector : sympFermSVOA.conformalVector = ωSF := rfl

/-- **The central charge is `-2`.** -/
@[simp] theorem sympFermSVOA_centralCharge : sympFermSVOA.centralCharge = -2 := rfl

/-- The Virasoro modes of the super VOA are the `LSF n`. -/
theorem sympFermSVOA_L (n : ℤ) : sympFermSVOA.L n = LSF n := (LSF_eq_mode n).symm

/-- The super VOA and the super near-VOA carry the same conformal data. -/
theorem sympFermSVOA_toSuperNearVOA : sympFermSVOA.toSuperNearVOA = sympFermSNVOA := rfl

end VOA.SympFerm
