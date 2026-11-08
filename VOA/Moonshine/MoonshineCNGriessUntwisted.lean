/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Moonshine.MoonshineCNGriessConway
import VOA.Moonshine.MoonshineCNGriessTable

/-!
# The dictionary between the untwisted part of `V♮₂` and `symMat × SpaceX`

This file builds the explicit map from the `W = 0` part `symMat × SpaceX` of the rational Griess
algebra `SpaceB` (AxiomMath's model, `VOA/Moonshine/MonsterGriess/`) to the weight-two space of
`V_Λ⁺ ⊆ V♮`, and proves that it carries `gmul` to the Griess product `u₍₁₎v` and `bform` to
`½ natForm`:

* `matDict M = Q_C(M^π)` — a rational `24 × 24` matrix in Axiom's coordinates (`r + 4j`, MOG row
  `r`, column `j`) is moved to our coordinates by the Golay permutation `π = piPerm`
  (`axiomToConway`), then sent to the `S²𝔥` state `conwayQuad`;
* `shortDict ζ x = Σ_c x_c ζ_c x_{α_c}`, where `α_c = shortVec c` is the minimal vector of our
  lattice that `π` carries to Axiom's representative `uvec c`, and `ζ : ShortIdx → ℂ` is a phase.

The `symMat · symMat`, `symMat · SpaceX` channels and the forms on `symMat` hold with no
hypothesis.  The `SpaceX · SpaceX` channel and the form on `SpaceX` need a coherent choice of
phases `ζ` and two facts about Axiom's coordinates on `Λ/2Λ`, collected in the hypothesis
structure `ShortSignDictionary ζ` (each field is a statement about lattice vectors, the Golay
cocode pairing and the cocycle `latticeCocycle` — no vertex algebra enters).

## Main results
* `axiomToConway` (`A ↦ (A_{πi,πj})` over `ℂ`): additive, `ℚ`-homogeneous, multiplicative,
  commutes with transpose, preserves the trace.
* `shortVec c`, `shortVec_norm` (`⟨α_c, α_c⟩ = 4`), `vec_shortVec` (`(α_c)ᵢ = (uvec c)_{πi}`),
  `quadForm_shortVec` (`y_cᵀ A^π y_c = qf c A`).
* unconditional channels: ⭐ `matDict_gmul_symBlock_symBlock`, ⭐ `shortDict_gmul_symBlock_shortBlock`,
  `shortDict_gmul_shortBlock_symBlock`, ⭐ `plusForm_matDict_matDict` (`= 2·tr(AB)`),
  `plusForm_matDict_shortDict` (`= 0`).
* conditional on `ShortSignDictionary ζ`: ⭐ `frameX0P_shortVec_mul_shortVec` (the product of two
  basis vectors), ⭐ `untwisted_gmul_shortBlock_shortBlock` (`SpaceX · SpaceX`),
  ⭐ `plusForm_shortDict_shortDict` (`= 2·Σ x_c y_c`).
* assembly: `untwistedDict ζ u = matDict u.1 + shortDict ζ u.2.1`; ⭐ `untwistedDict_gmul` and
  ⭐ `untwistedDict_form` on all `u, v` with zero `SpaceW` part; ⭐ `vnat_untwistedDict_gmul`,
  `vnat_untwistedDict_form` — the same statements inside `V♮` (Griess product of `VnatVOA`,
  form `natForm`).

## Status
The `ShortSignDictionary` hypothesis is the exact remainder of the untwisted block; see the
docstring of the structure for what discharges each field.
-/

set_option linter.style.longLine false

namespace VOA.Moonshine.GriessDictionary

open VOA VOA.Moonshine VOA.Moonshine.AutMonster VOA.Moonshine.SigmaTop VOA.Moonshine.TrialityTw
open VOA.LatGen VOA.IntegralLattice HeisenbergN
open VOA.Moonshine.ConwayNorton.M8
open VOA.Moonshine.MonsterGriess VOA.Moonshine.MonsterGriess.Spin VOA.Moonshine.MonsterGriess.Code
open VOA.Moonshine.MonsterGriess.LeechMatch (vec leechEquiv leechEquiv_symm_apply piPerm
  leechEquiv_mem_minVecs_iff)
open Matrix

/-! ## §1  From Axiom's coordinates to Conway's -/

/-- `A ↦ (A_{πi,πj})`, read in `ℂ`: a matrix in Axiom's coordinates, in our Conway coordinates. -/
noncomputable def axiomToConway (M : Matrix (Fin 24) (Fin 24) ℚ) : Matrix (Fin 24) (Fin 24) ℂ :=
  Matrix.of fun i j => (M (piPerm i) (piPerm j) : ℂ)

theorem axiomToConway_apply (M : Matrix (Fin 24) (Fin 24) ℚ) (i j : Fin 24) :
    axiomToConway M i j = (M (piPerm i) (piPerm j) : ℂ) := rfl

theorem axiomToConway_add (M N : Matrix (Fin 24) (Fin 24) ℚ) :
    axiomToConway (M + N) = axiomToConway M + axiomToConway N := by
  ext i j
  simp [axiomToConway_apply]

theorem axiomToConway_zero : axiomToConway 0 = 0 := by
  ext i j
  simp [axiomToConway_apply]

theorem axiomToConway_smul (q : ℚ) (M : Matrix (Fin 24) (Fin 24) ℚ) :
    axiomToConway (q • M) = (q : ℂ) • axiomToConway M := by
  ext i j
  simp [axiomToConway_apply]

theorem axiomToConway_mul (M N : Matrix (Fin 24) (Fin 24) ℚ) :
    axiomToConway (M * N) = axiomToConway M * axiomToConway N := by
  ext i j
  simp only [axiomToConway_apply, Matrix.mul_apply]
  push_cast
  exact (Equiv.sum_comp piPerm (fun k => (M (piPerm i) k : ℂ) * (N k (piPerm j) : ℂ))).symm

theorem axiomToConway_transpose (M : Matrix (Fin 24) (Fin 24) ℚ) :
    axiomToConway Mᵀ = (axiomToConway M)ᵀ := by
  ext i j
  simp [axiomToConway_apply]

theorem trace_axiomToConway (M : Matrix (Fin 24) (Fin 24) ℚ) :
    trace (axiomToConway M) = ((trace M : ℚ) : ℂ) := by
  simp only [trace, diag, axiomToConway_apply]
  push_cast
  exact Equiv.sum_comp piPerm (fun k => (M k k : ℂ))

/-- The additive map `M ↦ Q_C(M^π)` from rational matrices (Axiom's coordinates) to `V_Λ⁺`. -/
noncomputable def matDict : Matrix (Fin 24) (Fin 24) ℚ →+ VPlus where
  toFun M := conwayQuad (axiomToConway M)
  map_zero' := by rw [axiomToConway_zero, map_zero]
  map_add' M N := by rw [axiomToConway_add, map_add]

theorem matDict_apply (M : Matrix (Fin 24) (Fin 24) ℚ) :
    matDict M = conwayQuad (axiomToConway M) := rfl

theorem matDict_smul (q : ℚ) (M : Matrix (Fin 24) (Fin 24) ℚ) :
    matDict (q • M) = (q : ℂ) • matDict M := by
  rw [matDict_apply, axiomToConway_smul, map_smul, matDict_apply]

theorem matDict_mem_grading_two (M : Matrix (Fin 24) (Fin 24) ℚ) :
    matDict M ∈ leechVOAPlus.grading 2 :=
  conwayQuad_mem_grading_two _

/-! ## §2  The minimal vectors `α_c` attached to the short classes -/

theorem neg_mem_minVecs {u : Fin 24 → ℤ} (hu : u ∈ minVecs) : -u ∈ minVecs :=
  ⟨neg_mem_codeLattice allOnes_mem_C hu.1, by simpa [codeForm] using hu.2⟩

theorem uvec_mem_minVecs (c : ShortIdx) : uvec c ∈ minVecs := by
  unfold uvec
  split_ifs
  · exact c.2.choose_spec.1
  · exact neg_mem_minVecs c.2.choose_spec.1

/-- `α_c`: the minimal vector of our Leech lattice that `π` carries to Axiom's `uvec c`. -/
noncomputable def shortVec (c : ShortIdx) : leech.carrier :=
  leechEquiv.symm ⟨uvec c, (uvec_mem_minVecs c).1⟩

theorem leechEquiv_shortVec (c : ShortIdx) :
    (leechEquiv (shortVec c) : Fin 24 → ℤ) = uvec c := by
  rw [shortVec, AddEquiv.apply_symm_apply]

theorem vec_shortVec (c : ShortIdx) (i : Fin 24) : vec (shortVec c) i = uvec c (piPerm i) :=
  leechEquiv_symm_apply _ i

theorem shortVec_norm (c : ShortIdx) : leech.form (shortVec c) (shortVec c) = 4 := by
  rw [← leechEquiv_mem_minVecs_iff, leechEquiv_shortVec]
  exact uvec_mem_minVecs c

theorem shortVec_ne_zero (c : ShortIdx) : shortVec c ≠ 0 := by
  intro h
  have := shortVec_norm c
  rw [h] at this
  simp at this

/-- `y_cᵀ A^π y_c = qf c A`: the Conway-coordinate quadratic form of `α_c` is Axiom's `qf`. -/
theorem quadForm_shortVec (c : ShortIdx) (M : Matrix (Fin 24) (Fin 24) ℚ) :
    (fun i => (vec (shortVec c) i : ℂ)) ⬝ᵥ (axiomToConway M *ᵥ fun i => (vec (shortVec c) i : ℂ))
      = (qf c M : ℂ) := by
  simp only [dotProduct, mulVec, axiomToConway_apply, vec_shortVec, qf, uQ]
  push_cast
  have h : ∀ k : Fin 24, ∑ j, (M k (piPerm j) : ℂ) * (uvec c (piPerm j) : ℂ)
      = ∑ j, (M k j : ℂ) * (uvec c j : ℂ) := fun k =>
    Equiv.sum_comp piPerm (fun j => (M k j : ℂ) * (uvec c j : ℂ))
  simp only [h]
  exact Equiv.sum_comp piPerm (fun i => (uvec c i : ℂ) * ∑ j, (M i j : ℂ) * (uvec c j : ℂ))

theorem frameX0P_neg_eq (β : leech.carrier) : frameX0P (-β) = frameX0P β := by
  apply Subtype.ext
  change latChargeGen leech (-β) + latChargeGen leech (- -β)
    = latChargeGen leech β + latChargeGen leech (-β)
  rw [neg_neg, add_comm]

/-! ## §3  The unconditional channels -/

/-- The short-class part of the dictionary: `x ↦ Σ_c x_c ζ_c x_{α_c}`. -/
noncomputable def shortDict (ζ : ShortIdx → ℂ) : SpaceX →+ VPlus where
  toFun x := ∑ c, ((x c : ℂ) * ζ c) • frameX0P (shortVec c)
  map_zero' := by simp
  map_add' x y := by simp [add_mul, add_smul, Finset.sum_add_distrib]

theorem shortDict_apply (ζ : ShortIdx → ℂ) (x : SpaceX) :
    shortDict ζ x = ∑ c, ((x c : ℂ) * ζ c) • frameX0P (shortVec c) := rfl

theorem shortDict_mem_grading_two (ζ : ShortIdx → ℂ) (x : SpaceX) :
    shortDict ζ x ∈ leechVOAPlus.grading 2 :=
  Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _
    (frameX0P_mem_grading_two (shortVec_norm c))

theorem axiomToConway_symm (A : symMat) :
    (axiomToConway (A : Matrix (Fin 24) (Fin 24) ℚ))ᵀ = axiomToConway A := by
  rw [← axiomToConway_transpose, mem_symMat.1 A.2]

/-- ⭐ **`symMat · symMat`**: `matDict (A·B) = matDict A ₍₁₎ matDict B`. -/
theorem matDict_gmul_symBlock_symBlock (A B : symMat) :
    matDict (gmul (symBlock A) (symBlock B)).1
      = leechVOAPlus.smul (matDict A) 1 (matDict B) := by
  rw [gmul_symBlock_symBlock_fst, matDict_smul, matDict_apply, matDict_apply, matDict_apply,
    conwayQuad_one_conwayQuad_of_symm (axiomToConway_symm A) (axiomToConway_symm B),
    axiomToConway_add, axiomToConway_mul, axiomToConway_mul]
  norm_num

/-- ⭐ **`symMat · SpaceX`**: `shortDict (A·x) = matDict A ₍₁₎ shortDict x`. -/
theorem shortDict_gmul_symBlock_shortBlock (ζ : ShortIdx → ℂ) (A : symMat) (x : SpaceX) :
    shortDict ζ (gmul (symBlock A) (shortBlock x)).2.1
      = leechVOAPlus.smul (matDict A) 1 (shortDict ζ x) := by
  rw [gmul_symBlock_shortBlock_snd_fst, shortDict_apply, shortDict_apply, smul_sum_right']
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [PreVertexAlgebra.smul_smul_right, matDict_apply, conwayQuad_one_frameX0P,
    quadForm_shortVec, smul_smul]
  congr 1
  push_cast
  ring

theorem shortDict_gmul_shortBlock_symBlock (ζ : ShortIdx → ℂ) (x : SpaceX) (A : symMat) :
    shortDict ζ (gmul (shortBlock x) (symBlock A)).2.1
      = leechVOAPlus.smul (shortDict ζ x) 1 (matDict A) := by
  rw [plus_one_comm (shortDict_mem_grading_two ζ x) (matDict_mem_grading_two _),
    ← shortDict_gmul_symBlock_shortBlock, gmul_shortBlock_symBlock_snd_fst,
    gmul_symBlock_shortBlock_snd_fst]

/-- ⭐ **The form on `symMat`**: `⟨matDict A, matDict B⟩ = 2·bform(A, B)`. -/
theorem plusForm_matDict_matDict (A B : symMat) :
    plusForm (matDict A) (matDict B) = 2 * (bform (symBlock A) (symBlock B) : ℂ) := by
  rw [matDict_apply, matDict_apply, plusForm_conwayQuad_conwayQuad_of_symm (axiomToConway_symm B),
    ← axiomToConway_mul, trace_axiomToConway, bform_symBlock_symBlock]

theorem plusForm_matDict_shortDict (ζ : ShortIdx → ℂ) (M : Matrix (Fin 24) (Fin 24) ℚ)
    (x : SpaceX) : plusForm (matDict M) (shortDict ζ x) = 0 := by
  rw [shortDict_apply, map_sum]
  refine Finset.sum_eq_zero fun c _ => ?_
  rw [map_smul, matDict_apply, plusForm_conwayQuad_frameX0P _ (shortVec_ne_zero c), smul_zero]

theorem plusForm_shortDict_matDict (ζ : ShortIdx → ℂ) (M : Matrix (Fin 24) (Fin 24) ℚ)
    (x : SpaceX) : plusForm (shortDict ζ x) (matDict M) = 0 := by
  rw [plusForm_apply, Nondeg.latForm_symm, ← plusForm_apply, plusForm_matDict_shortDict]

/-! ## §4  The short-class channel, from a sign dictionary -/

/-- **The data that makes the short-class block of the dictionary an isometric algebra map.**
For a phase function `ζ : ShortIdx → ℂ`:

* `sq` — `ζ_c² ε(α_c, α_c) = 1` (the form `⟨x_α, x_α⟩ = 2ε(α,α)` against `bform = 1`);
* `pm_injective` — distinct short classes have distinct `±`-pairs `±α_c`;
* `sum_shape`, `sum_exists` — `c = d + e` in Axiom's coordinates `C × Cocode` happens exactly when
  `⟨α_d, α_e⟩ = ∓2`, and then `α_c = ±(α_d ± α_e)`;
* `sign_neg_two`, `sign_two` — Axiom's structure constant `sgn(pair(e.a, d.δ))` against the
  cocycle `ε` of our lattice VOA, corrected by the phases.

`pm_injective`, `sum_shape`, `sum_exists` follow from additivity and injectivity of Axiom's
`phi0 : C × Cocode → Λ/2Λ` (the source's `lamT_add`, `phi0Equiv`, not ported) and the fact that
the classes of `Λ/2Λ` with a norm-`4` representative contain exactly `±` one minimal vector
(`LeechMatch.classOf_eq_iff`).  `sq`, `sign_neg_two`, `sign_two` together say that `ζ` is a
quadratic refinement of the symmetric form `ε̄ + τ` on `Λ/2Λ`; its existence needs the commutator
identity `pair(e.a, d.δ) + pair(d.a, e.δ) ≡ ⟨α_d, α_e⟩ (mod 2)` on Axiom's side. -/
structure ShortSignDictionary (ζ : ShortIdx → ℂ) : Prop where
  sq : ∀ c, ζ c ^ 2 * latticeCocycle leech (shortVec c) (shortVec c) = 1
  pm_injective : ∀ c d : ShortIdx, (shortVec d = shortVec c ∨ shortVec d = -shortVec c) → d = c
  sum_shape : ∀ d e c : ShortIdx, c.1 = d.1 + e.1 →
    (leech.form (shortVec d) (shortVec e) = -2 ∧
      (shortVec c = shortVec d + shortVec e ∨ shortVec c = -(shortVec d + shortVec e))) ∨
    (leech.form (shortVec d) (shortVec e) = 2 ∧
      (shortVec c = shortVec e - shortVec d ∨ shortVec c = -(shortVec e - shortVec d)))
  sum_exists : ∀ d e : ShortIdx, (leech.form (shortVec d) (shortVec e) = -2 ∨
    leech.form (shortVec d) (shortVec e) = 2) → ∃ c : ShortIdx, c.1 = d.1 + e.1
  sign_neg_two : ∀ d e c : ShortIdx, c.1 = d.1 + e.1 → leech.form (shortVec d) (shortVec e) = -2 →
    (MonsterGriess.sgn (pair e.1.1 d.1.2) : ℂ) * ζ c = ζ d * ζ e * latticeCocycle leech (shortVec d) (shortVec e)
  sign_two : ∀ d e c : ShortIdx, c.1 = d.1 + e.1 → leech.form (shortVec d) (shortVec e) = 2 →
    (MonsterGriess.sgn (pair e.1.1 d.1.2) : ℂ) * ζ c = ζ d * ζ e * latticeCocycle leech (shortVec d) (-shortVec e)

theorem tau_of_eq {d e c : ShortIdx} (h : c.1 = d.1 + e.1) : tau d e c = MonsterGriess.sgn (pair e.1.1 d.1.2) := by
  simp only [tau]
  rw [if_pos h]

theorem tau_of_ne {d e c : ShortIdx} (h : c.1 ≠ d.1 + e.1) : tau d e c = 0 := by
  simp only [tau]
  rw [if_neg h]

/-- The `τ`-sum collapses on the unique class `c₀ = d + e`. -/
theorem sum_tau_smul_of_eq (ζ : ShortIdx → ℂ) {d e c₀ : ShortIdx} (h : c₀.1 = d.1 + e.1) :
    ∑ c, ((tau d e c : ℂ) * ζ c) • frameX0P (shortVec c)
      = ((MonsterGriess.sgn (pair e.1.1 d.1.2) : ℂ) * ζ c₀) • frameX0P (shortVec c₀) := by
  rw [Finset.sum_eq_single c₀]
  · rw [tau_of_eq h]
  · intro c _ hc
    rw [tau_of_ne (fun h' => hc (Subtype.ext (h'.trans h.symm))), Rat.cast_zero, zero_mul,
      zero_smul]
  · intro h'
    exact absurd (Finset.mem_univ c₀) h'

theorem sum_tau_smul_of_forall_ne (ζ : ShortIdx → ℂ) {d e : ShortIdx}
    (h : ∀ c : ShortIdx, c.1 ≠ d.1 + e.1) :
    ∑ c, ((tau d e c : ℂ) * ζ c) • frameX0P (shortVec c) = 0 :=
  Finset.sum_eq_zero fun c _ => by rw [tau_of_ne (h c), Rat.cast_zero, zero_mul, zero_smul]

/-- `Umat c / 8` is `β(−1)²𝟙` for `β = α_c`. -/
theorem matDict_Umat (c : ShortIdx) :
    matDict ((8 : ℚ)⁻¹ • Umat c) = (dV (shortVec c) (shortVec c) : VPlus) := by
  rw [matDict_smul, matDict_apply, dV_self_eq_conwayQuad, map_smul]
  congr 2
  · push_cast; rfl
  · ext i j
    simp [axiomToConway_apply, Umat, uQ, vecMulVec_apply, vec_shortVec]

variable {ζ : ShortIdx → ℂ}

/-- ⭐ **The product of two short basis vectors**, from a sign dictionary:
`ζ_d ζ_e · x_{α_d} ₍₁₎ x_{α_e} = [d = e]·(β(−1)²𝟙 for β = α_d) + Σ_c τ(d,e,c) ζ_c x_{α_c}`. -/
theorem frameX0P_shortVec_mul_shortVec (hζ : ShortSignDictionary ζ) (d e : ShortIdx) :
    (ζ d * ζ e) • leechVOAPlus.smul (frameX0P (shortVec d)) 1 (frameX0P (shortVec e))
      = (if d = e then matDict ((8 : ℚ)⁻¹ • Umat d) else 0)
        + ∑ c, ((tau d e c : ℂ) * ζ c) • frameX0P (shortVec c) := by
  classical
  have hd := shortVec_norm d
  have he := shortVec_norm e
  by_cases hde : d = e
  · subst hde
    rw [if_pos rfl, frameX0P_one_frameX0P_self hd, smul_smul,
      latticeCocycle_neg_right, ← sq, hζ.sq d, one_smul, matDict_Umat,
      sum_tau_smul_of_forall_ne ζ, add_zero]
    intro c hc
    rcases hζ.sum_shape d d c hc with ⟨h, -⟩ | ⟨h, -⟩ <;> omega
  · rw [if_neg hde, zero_add]
    rcases leech_form_cases_of_normFour hd he with h | h | h | h | h | h | h
    · exact absurd (hζ.pm_injective d e (Or.inr ((leech_form_neg_four_iff_of_normFour hd he).1 h))).symm hde
    · obtain ⟨c₀, hc₀⟩ := hζ.sum_exists d e (Or.inl h)
      rw [frameX0P_one_frameX0P_of_form_neg_two h, sum_tau_smul_of_eq ζ hc₀, smul_smul,
        hζ.sign_neg_two d e c₀ hc₀ h]
      rcases hζ.sum_shape d e c₀ hc₀ with ⟨-, h' | h'⟩ | ⟨h2, -⟩
      · rw [h']
      · rw [h', frameX0P_neg_eq]
      · omega
    · rw [frameX0P_one_frameX0P_of_form_small (by omega) (by omega), smul_zero,
        sum_tau_smul_of_forall_ne ζ]
      intro c hc
      rcases hζ.sum_shape d e c hc with ⟨h', -⟩ | ⟨h', -⟩ <;> omega
    · rw [frameX0P_one_frameX0P_of_form_small (by omega) (by omega), smul_zero,
        sum_tau_smul_of_forall_ne ζ]
      intro c hc
      rcases hζ.sum_shape d e c hc with ⟨h', -⟩ | ⟨h', -⟩ <;> omega
    · rw [frameX0P_one_frameX0P_of_form_small (by omega) (by omega), smul_zero,
        sum_tau_smul_of_forall_ne ζ]
      intro c hc
      rcases hζ.sum_shape d e c hc with ⟨h', -⟩ | ⟨h', -⟩ <;> omega
    · obtain ⟨c₀, hc₀⟩ := hζ.sum_exists d e (Or.inr h)
      rw [frameX0P_one_frameX0P_of_form_two h, sum_tau_smul_of_eq ζ hc₀, smul_smul,
        hζ.sign_two d e c₀ hc₀ h]
      rcases hζ.sum_shape d e c₀ hc₀ with ⟨h2, -⟩ | ⟨-, h' | h'⟩
      · omega
      · rw [h']
      · rw [h', frameX0P_neg_eq]
    · exact absurd (hζ.pm_injective d e (Or.inl ((leech_form_four_iff_of_normFour hd he).1 h))).symm hde

/-- ⭐ **`SpaceX · SpaceX`**, from a sign dictionary: the dictionary carries Axiom's product of two
short-class vectors (its `symMat` and `SpaceX` parts) to the Griess product. -/
theorem untwisted_gmul_shortBlock_shortBlock (hζ : ShortSignDictionary ζ) (x y : SpaceX) :
    matDict (gmul (shortBlock x) (shortBlock y)).1 + shortDict ζ (gmul (shortBlock x) (shortBlock y)).2.1
      = leechVOAPlus.smul (shortDict ζ x) 1 (shortDict ζ y) := by
  classical
  have hR : leechVOAPlus.smul (shortDict ζ x) 1 (shortDict ζ y)
      = ∑ d, ∑ e, ((x d : ℂ) * (y e : ℂ)) •
          ((if d = e then matDict ((8 : ℚ)⁻¹ • Umat d) else 0)
            + ∑ c, ((tau d e c : ℂ) * ζ c) • frameX0P (shortVec c)) := by
    rw [shortDict_apply, smul_sum_left]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [PreVertexAlgebra.smul_smul_left, shortDict_apply, smul_sum_right', Finset.smul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [PreVertexAlgebra.smul_smul_right, ← frameX0P_shortVec_mul_shortVec hζ, smul_smul,
      smul_smul]
    congr 1
    ring
  rw [hR]
  simp only [smul_add, Finset.sum_add_distrib, smul_ite, smul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
  congr 1
  · rw [gmul_shortBlock_shortBlock_fst]
    change matDict ((8 : ℚ)⁻¹ • ∑ c, (x c * y c) • Umat c) = _
    rw [Finset.smul_sum, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [smul_comm, matDict_smul]
    push_cast
    rfl
  · rw [gmul_shortBlock_shortBlock_snd_fst, shortDict_apply]
    simp only [Finset.smul_sum, smul_smul]
    conv_rhs => enter [2, d]; rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    push_cast
    rw [Finset.sum_mul, Finset.sum_smul]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.sum_mul, Finset.sum_smul]
    refine Finset.sum_congr rfl fun e _ => ?_
    congr 1
    ring

/-- ⭐ **The form on `SpaceX`**, from a sign dictionary: `⟨shortDict x, shortDict y⟩ = 2·Σ x_c y_c`. -/
theorem plusForm_shortDict_shortDict (hζ : ShortSignDictionary ζ) (x y : SpaceX) :
    plusForm (shortDict ζ x) (shortDict ζ y) = 2 * (bform (shortBlock x) (shortBlock y) : ℂ) := by
  classical
  rw [bform_shortBlock_shortBlock, shortDict_apply, shortDict_apply]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    plusForm_frameX0P_frameX0P (shortVec_norm _)]
  have hc : ∀ c d : ShortIdx, (shortVec d = shortVec c ∨ shortVec d = -shortVec c) ↔ d = c := by
    intro c d
    refine ⟨hζ.pm_injective c d, ?_⟩
    rintro rfl
    exact Or.inl rfl
  simp only [hc, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  have := hζ.sq c
  linear_combination (2 * (x c : ℂ) * (y c : ℂ)) * this


/-! ## §5  The dictionary on the whole untwisted part -/

variable (ζ) in
/-- **The dictionary on the untwisted part** `symMat × SpaceX`: `u ↦ matDict u.1 + shortDict ζ u.2.1`
(the `SpaceW` component, the twisted block, is not read). -/
noncomputable def untwistedDict : SpaceB →+ VPlus where
  toFun u := matDict u.1 + shortDict ζ u.2.1
  map_zero' := by
    change matDict ((0 : symMat) : Matrix (Fin 24) (Fin 24) ℚ) + shortDict ζ 0 = 0
    rw [Submodule.coe_zero, map_zero, map_zero, add_zero]
  map_add' u v := by
    change matDict ((u.1 + v.1 : symMat) : Matrix (Fin 24) (Fin 24) ℚ) + shortDict ζ (u.2.1 + v.2.1)
      = matDict u.1 + shortDict ζ u.2.1 + (matDict v.1 + shortDict ζ v.2.1)
    rw [Submodule.coe_add, map_add, map_add]
    abel

theorem untwistedDict_apply (u : SpaceB) : untwistedDict ζ u = matDict u.1 + shortDict ζ u.2.1 :=
  rfl

theorem untwistedDict_symBlock (A : symMat) : untwistedDict ζ (symBlock A) = matDict A := by
  rw [untwistedDict_apply]
  change matDict A + shortDict ζ 0 = matDict A
  rw [map_zero, add_zero]

theorem untwistedDict_shortBlock (x : SpaceX) : untwistedDict ζ (shortBlock x) = shortDict ζ x := by
  rw [untwistedDict_apply]
  change matDict ((0 : symMat) : Matrix (Fin 24) (Fin 24) ℚ) + shortDict ζ x = shortDict ζ x
  rw [Submodule.coe_zero, map_zero, zero_add]

theorem untwistedDict_mem_grading_two (u : SpaceB) :
    untwistedDict ζ u ∈ leechVOAPlus.grading 2 :=
  Submodule.add_mem _ (matDict_mem_grading_two _) (shortDict_mem_grading_two ζ _)

theorem untwistedDict_gmul_symBlock_symBlock (A B : symMat) :
    untwistedDict ζ (gmul (symBlock A) (symBlock B))
      = leechVOAPlus.smul (matDict A) 1 (matDict B) := by
  have h0 : (gmul (symBlock A) (symBlock B)).2.1 = 0 := by
    rw [gmul_symBlock_symBlock_snd]; rfl
  rw [untwistedDict_apply, h0, map_zero, add_zero, matDict_gmul_symBlock_symBlock]

theorem untwistedDict_gmul_symBlock_shortBlock (A : symMat) (x : SpaceX) :
    untwistedDict ζ (gmul (symBlock A) (shortBlock x))
      = leechVOAPlus.smul (matDict A) 1 (shortDict ζ x) := by
  rw [untwistedDict_apply, gmul_symBlock_shortBlock_fst, map_zero, zero_add,
    shortDict_gmul_symBlock_shortBlock]

theorem untwistedDict_gmul_shortBlock_symBlock (x : SpaceX) (A : symMat) :
    untwistedDict ζ (gmul (shortBlock x) (symBlock A))
      = leechVOAPlus.smul (shortDict ζ x) 1 (matDict A) := by
  rw [untwistedDict_apply, gmul_shortBlock_symBlock_fst, map_zero, zero_add,
    shortDict_gmul_shortBlock_symBlock]

theorem untwistedDict_gmul_shortBlock_shortBlock (hζ : ShortSignDictionary ζ) (x y : SpaceX) :
    untwistedDict ζ (gmul (shortBlock x) (shortBlock y))
      = leechVOAPlus.smul (shortDict ζ x) 1 (shortDict ζ y) := by
  rw [untwistedDict_apply, untwisted_gmul_shortBlock_shortBlock hζ]

theorem eq_symBlock_add_shortBlock {u : SpaceB} (hu : u.2.2 = 0) :
    u = symBlock u.1 + shortBlock u.2.1 := by
  conv_lhs => rw [spaceB_eq_blocks u]
  rw [hu, show spinBlock 0 = 0 from rfl, add_zero]

/-- ⭐ **The untwisted dictionary is multiplicative** (given a sign dictionary): for `u, v` with
zero `SpaceW` part, `untwistedDict (gmul u v) = (untwistedDict u)₍₁₎(untwistedDict v)` in `V_Λ⁺`. -/
theorem untwistedDict_gmul (hζ : ShortSignDictionary ζ) {u v : SpaceB} (hu : u.2.2 = 0)
    (hv : v.2.2 = 0) :
    untwistedDict ζ (gmul u v) = leechVOAPlus.smul (untwistedDict ζ u) 1 (untwistedDict ζ v) := by
  rw [eq_symBlock_add_shortBlock hu, eq_symBlock_add_shortBlock hv]
  generalize u.1 = A
  generalize u.2.1 = x
  generalize v.1 = B
  generalize v.2.1 = y
  simp only [map_add, LinearMap.add_apply, untwistedDict_symBlock, untwistedDict_shortBlock,
    PreVertexAlgebra.smul_add_left, PreVertexAlgebra.smul_add_right,
    untwistedDict_gmul_symBlock_symBlock, untwistedDict_gmul_symBlock_shortBlock,
    untwistedDict_gmul_shortBlock_symBlock, untwistedDict_gmul_shortBlock_shortBlock hζ]

/-- ⭐ **The untwisted dictionary is an isometry up to the factor `2`** (given a sign dictionary):
`plusForm (untwistedDict u) (untwistedDict v) = 2·bform u v` for `u, v` with zero `SpaceW` part. -/
theorem untwistedDict_form (hζ : ShortSignDictionary ζ) {u v : SpaceB} (hu : u.2.2 = 0)
    (hv : v.2.2 = 0) :
    plusForm (untwistedDict ζ u) (untwistedDict ζ v) = 2 * (bform u v : ℂ) := by
  have hb : bform u v = bform (symBlock u.1) (symBlock v.1)
      + bform (shortBlock u.2.1) (shortBlock v.2.1) := by
    rw [bform_apply, bform_symBlock_symBlock, bform_shortBlock_shortBlock, hu, hv]
    simp
  rw [untwistedDict_apply, untwistedDict_apply, hb, map_add, map_add, LinearMap.add_apply,
    LinearMap.add_apply, plusForm_matDict_matDict, plusForm_matDict_shortDict,
    plusForm_shortDict_matDict, plusForm_shortDict_shortDict hζ]
  push_cast
  ring

/-! ## §6  The same statements inside `V♮` -/

theorem untwistedDict_mem_vnat_grading_two (u : SpaceB) :
    ((untwistedDict ζ u, 0) : Vnat) ∈ VnatVOA.grading 2 := by
  rw [VnatVOA_grading, mem_gradingNat]
  exact ⟨untwistedDict_mem_grading_two u, Submodule.zero_mem _⟩

variable (ζ) in
/-- The untwisted dictionary as a map into the weight-two space of `V♮`. -/
noncomputable def untwistedDictNat (u : SpaceB) : VnatVOA.grading 2 :=
  ⟨(untwistedDict ζ u, 0), untwistedDict_mem_vnat_grading_two u⟩

/-- ⭐ **`V♮` form of the multiplicativity**: the Griess product of `VnatVOA` on the images. -/
theorem untwistedDictNat_gmul (hζ : ShortSignDictionary ζ) {u v : SpaceB} (hu : u.2.2 = 0)
    (hv : v.2.2 = 0) :
    untwistedDictNat ζ (gmul u v) = VnatVOA.griessMul (untwistedDictNat ζ u) (untwistedDictNat ζ v) := by
  apply Subtype.ext
  rw [VertexOperatorAlgebra.griessMul_coe]
  change ((untwistedDict ζ (gmul u v), 0) : Vnat)
    = VnatVOA.smul ((untwistedDict ζ u, 0) : Vnat) 1 ((untwistedDict ζ v, 0) : Vnat)
  rw [vnat_smul_untwisted, untwistedDict_gmul hζ hu hv]

/-- ⭐ **`V♮` form of the isometry**: `natForm` on the images is `2·bform`. -/
theorem untwistedDictNat_form (hζ : ShortSignDictionary ζ) {u v : SpaceB} (hu : u.2.2 = 0)
    (hv : v.2.2 = 0) :
    SimpleNat.natForm (untwistedDictNat ζ u : Vnat) (untwistedDictNat ζ v : Vnat)
      = 2 * (bform u v : ℂ) := by
  change SimpleNat.natForm ((untwistedDict ζ u, 0) : Vnat) ((untwistedDict ζ v, 0) : Vnat) = _
  rw [natForm_untwisted, untwistedDict_form hζ hu hv]

/-- The `symMat` block needs no sign data: `natForm` and the Griess product on `symMat` images. -/
theorem untwistedDictNat_gmul_symBlock (A B : symMat) :
    untwistedDictNat ζ (gmul (symBlock A) (symBlock B))
      = VnatVOA.griessMul (untwistedDictNat ζ (symBlock A)) (untwistedDictNat ζ (symBlock B)) := by
  apply Subtype.ext
  rw [VertexOperatorAlgebra.griessMul_coe]
  change ((untwistedDict ζ (gmul (symBlock A) (symBlock B)), 0) : Vnat)
    = VnatVOA.smul ((untwistedDict ζ (symBlock A), 0) : Vnat) 1 ((untwistedDict ζ (symBlock B), 0) : Vnat)
  rw [vnat_smul_untwisted, untwistedDict_gmul_symBlock_symBlock, untwistedDict_symBlock,
    untwistedDict_symBlock]

end VOA.Moonshine.GriessDictionary
