/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2
import VOA.Core.VertexOperatorAlgebra
import VOA.Core.Goddard
import VOA.Core.Dong
import VOA.Examples.HeisenbergVertex
import Mathlib.Tactic.FinCases

/-!
# The full affine `𝔰𝔩₂` VOA `𝒱(𝔰𝔩₂, k)` — the vertex-algebra layer

Builds on `Examples.AffineSl2` (the level-`k` realization on the single vacuum module
`WakModule k = 𝒱(𝔰𝔩₂, k) = U(ĝ)⧸J(k)`): the three currents `J k a m`, the FULL affine
commutator `current_comm`, the current fields `Jfield k a`, and their `N = 2` mutual
locality `Jfield_local`.

This file adds the **vertex-algebra superstructure** on `WakModule k`, reusing the
module-polymorphic Heisenberg recipe (`Core.Dong.nprod`/`IsField`/`dong_neg`,
`Core.Goddard.goddard_uniqueness`, `Core.VertexOperatorAlgebra`):

* **§A — the VOA grading bridge.** AffineLie grades `WakModule k` by `ℓ₀`-energy
  eigenspaces of eigenvalue `-(d)`, `d : ℕ` (`AffineLie.ell0_isInternal`,
  `eigenspace_finiteDimensional`, `eigenspace_zero_eq`, `eigenspace_eq_bot_of_not_energy`).
  We reindex to the VOA `ℤ`-grading `gradingZA k n := eigenspace (ell0Op) (-(n))`, and port
  `isInternal`, finite-dimensionality, `|0⟩ ∈ grading 0`, `grading 0 = ℂ·|0⟩`, and
  `positivity` (`n < 0 → grading n = ⊥`) — the VA1/VA5/CFT-type data.
* **§B — the current fields are `IsField`.** `Jfield k a` is lower-truncated on every
  state (regularity), so it enters the `nprod`/`dong_neg` machine.  The generator fields
  `genFieldA k a i := (i!)⁻¹ ∂_z^i J^a(z)` and the iterated normal product `YwordA` are
  built exactly as in `HeisenbergNVertex`.
* **§C — the Sugawara conformal vector.** `T(z) = (1/(2(k+2))) ∑_{a,b} κ⁻¹(a,b) :J^a J^b:(z)`
  with `h^∨ = 2`, `dim 𝔰𝔩₂ = 3`; the conformal vector `ω`, weight `2`, and the central
  charge `c = 3k/(k+2)` (`affineSl2_centralCharge_val`).

## ⚠ STALE — THE OBSTRUCTION BELOW WAS RESOLVED

The paragraph that follows is kept for the record but its **conclusion is obsolete**.  It reasons
that `YA` cannot be assembled because `WakModule k` has no free `Finsupp` basis.  That premise is
true; the conclusion drawn from it is not.  `Core.ReconstructionExistence.reconstruct` requires
only `hspan : Submodule.span ℂ (Set.range st) = ⊤` — **spanning, never a basis** — which
`negSpan_eq_top` supplies on a UEA quotient.  Well-definedness comes from Goddard uniqueness
(`ker S ≤ ker F`), not from a basis.

`Examples/AffineSl2Reconstruction.lean` carries this out, and the closed instance
`AffineVOA.affineSl2VOA_closed (k) (hk : k + 2 ≠ 0) : VertexOperatorAlgebra (WakModule k)`
exists at `Examples/AffineSl2Virasoro.lean:845`, axiom-clean and `pbw`-free.

## The recorded obstruction (historical; see §D)
The Heisenberg `YN` is `Finsupp.linearCombination ℂ (YmonN r k)` over the *free* monomial
basis of `FockN r = MvPolynomial (ℕ × Fin r) ℂ`.  `WakModule k = U(ĝ)⧸J(k)` is a
UEA-quotient: it is spanned by the creation words `negWord` (`negSpan_eq_top`) but carries
**no free `Finsupp` basis** — `VOA.pbw : PBWPrinciple` exposes affine-vacuum
nonvanishing and generic relative-induction bottom injectivity, not a free basis of creation
monomials. Hence the all-states map `YA : WakModule k →ₗ FormalDist (End (WakModule k))`
cannot be assembled by `linearCombination` over a basis, and the `PreVertexAlgebra` instance
shell cannot be closed axiom-cleanly here without the module-polymorphic *reconstruction
theorem* (build `Y` on a cyclic module from generating local fields).  The two ingredients
that ARE module-polymorphic — `nprod`/`dong_neg` locality and `goddard_uniqueness`
translation — are wired up on the generating fields; the missing piece is the basis-free
`YA` itself.  §D records the exact target signature.

## Axioms
The current-algebra inputs (`current_comm`, `Jfield_local`, `Examples.AffineSl2`) are `pbw`-free.
`VOA.pbw` enters only through `vacuumA_ne_zero` (via `vacuumVector_ne_zero`); a `pbw`-free proof of
the same fact is `Wak.vacuumA_ne_zero_free` (`Examples.WakimotoFree`, needs `k + 2 ≠ 0`).

## References
* Gannon §3.2, §5.2.2 (Sugawara, eq. 5.2.6); Kac §10, §12; Frenkel–Zhu; Lepowsky–Li Ch. 6.
-/

namespace VOA.AffineVOA

open scoped BigOperators
open VOA.AffineLie
open Module (End)

universe u

/-! ## §A  The VOA grading bridge — reindex the `ℓ₀`-energy eigenspaces

AffineLie grades `WakModule k` by `Module.End.eigenspace (ell0Op …) μ`, nonzero only at
`μ = -(d)`, `d : ℕ` (energies `≥ 0`).  The VOA grading wants `grading n` for `n : ℤ`, with
`|0⟩ ∈ grading 0` and `grading n = ⊥` for `n < 0`.  We set
`gradingZA k n := eigenspace (ell0Op) (-(n : ℂ))`. -/

/-- The energy operator `ℓ₀` on `WakModule k` (the AffineLie `ell0Op`). -/
noncomputable def ell0OpA (k : ℂ) : End ℂ (WakModule k) :=
  ell0Op kappaForm kappaForm_isInvariant k

/-- The VOA `ℤ`-grading on `WakModule k`: the `ℓ₀`-eigenspace of eigenvalue `-n` (so the
energy-`d` piece is `grading d`, `|0⟩ ∈ grading 0`). -/
noncomputable def gradingZA (k : ℂ) (n : ℤ) : Submodule ℂ (WakModule k) :=
  Module.End.eigenspace (ell0OpA k) (-(n : ℂ))

theorem gradingZA_def (k : ℂ) (n : ℤ) :
    gradingZA k n = Module.End.eigenspace (ell0OpA k) (-(n : ℂ)) := rfl

/-- The reindexing `n : ℤ ↦ -(n : ℂ)` is injective: it distinguishes the VOA degrees. -/
theorem negCast_injective : Function.Injective (fun n : ℤ => (-(n : ℂ))) := by
  intro a b h
  simp only [neg_inj] at h
  exact_mod_cast h

/-- Off the image of `n ↦ -(n:ℂ)` — i.e. at any non-integer eigenvalue — the `ℓ₀`-eigenspace
is `⊥`. (Every nonzero energy is `-(d)` for `d : ℕ ⊆ ℤ`.) -/
theorem eigenspace_eq_bot_of_not_int (k : ℂ) (μ : ℂ) (hμ : ∀ n : ℤ, μ ≠ -(n : ℂ)) :
    Module.End.eigenspace (ell0OpA k) μ = ⊥ := by
  refine eigenspace_eq_bot_of_not_energy kappaForm kappaForm_isInvariant k μ ?_
  intro d
  exact hμ (d : ℤ) ∘ (by intro h; rwa [Int.cast_natCast])

/-- **The `ℓ₀`-eigenspaces of `WakModule k` are `iSupIndep`** — the spectral decomposition
of the energy operator. -/
theorem eigenspaces_iSupIndep_A (k : ℂ) :
    iSupIndep (fun μ : ℂ => Module.End.eigenspace (ell0OpA k) μ) :=
  Module.End.eigenspaces_iSupIndep (ell0OpA k)

/-- **The VOA grading is `iSupIndep`**: reindex the eigenspace independence along the
injection `n ↦ -(n:ℂ)`. -/
theorem gradingZA_iSupIndep (k : ℂ) : iSupIndep (gradingZA k) :=
  (eigenspaces_iSupIndep_A k).comp negCast_injective

/-- **The VOA grading spans `WakModule k`**: every energy eigenspace appears at an integer
degree, and the eigenspaces span (`AffineLie.iSup_eigenspace_eq_top`). -/
theorem gradingZA_iSup_eq_top (k : ℂ) : ⨆ n : ℤ, gradingZA k n = ⊤ := by
  rw [eq_top_iff, ← iSup_eigenspace_eq_top kappaForm kappaForm_isInvariant k]
  refine iSup_le fun μ => ?_
  by_cases h : ∃ n : ℤ, μ = -(n : ℂ)
  · obtain ⟨n, rfl⟩ := h
    exact le_iSup (gradingZA k) n
  · simp only [not_exists] at h
    rw [show ell0Op kappaForm kappaForm_isInvariant k = ell0OpA k from rfl,
      eigenspace_eq_bot_of_not_int k μ h]
    exact bot_le

/-- **VA1/VA5 grading datum**: `WakModule k` is the internal direct sum of its VOA-graded
pieces `gradingZA k n` (Gannon §3.2 `ℓ₀`-grading, reindexed to the VOA convention). -/
theorem gradingZA_isInternal (k : ℂ) : DirectSum.IsInternal (gradingZA k) :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (gradingZA_iSupIndep k) (gradingZA_iSup_eq_top k)

/-- Each VOA-graded piece is finite-dimensional (`AffineLie.eigenspace_finiteDimensional`
for finite-dimensional `𝔰𝔩₂`). -/
theorem gradingZA_finiteDimensional (k : ℂ) (n : ℤ) :
    FiniteDimensional ℂ (gradingZA k n) :=
  eigenspace_finiteDimensional kappaForm kappaForm_isInvariant k (-(n : ℂ))

/-- The **vacuum vector** `|0⟩ ∈ WakModule k`. -/
noncomputable def vacuumA (k : ℂ) : WakModule k :=
  vacuumVector kappaForm kappaForm_isInvariant k

/-- The vacuum is nonzero by the PBW theorem `VOA.pbw` (via `vacuumVector_ne_zero`). -/
theorem vacuumA_ne_zero (k : ℂ) : vacuumA k ≠ 0 :=
  vacuumVector_ne_zero kappaForm kappaForm_isInvariant k

/-- **Degree `0` is `ℂ·|0⟩`** (CFT-type, part 1): the top energy piece is spanned by the
vacuum (`AffineLie.eigenspace_zero_eq`). -/
theorem gradingZA_zero_eq_span_vacuum (k : ℂ) :
    gradingZA k 0 = Submodule.span ℂ {vacuumA k} := by
  rw [gradingZA_def, ell0OpA, show (-(0 : ℤ) : ℂ) = 0 from by norm_num,
    eigenspace_zero_eq kappaForm kappaForm_isInvariant k]
  rfl

/-- The vacuum lies in degree `0`: `|0⟩ ∈ grading 0`. -/
theorem vacuumA_mem_gradingZA_zero (k : ℂ) : vacuumA k ∈ gradingZA k 0 := by
  rw [gradingZA_zero_eq_span_vacuum]
  exact Submodule.mem_span_singleton_self _

/-- **CFT-type, part 1** in the `Submodule.span` shape `ℂ ∙ |0⟩` (the `vacuum_grade` field). -/
theorem gradingZA_zero_eq_smul_vacuum (k : ℂ) :
    gradingZA k 0 = (ℂ ∙ vacuumA k) :=
  gradingZA_zero_eq_span_vacuum k

/-- **CFT-type, part 2 / positivity**: `grading n = ⊥` for `n < 0` (the energies are `≥ 0`,
so there are no negative-energy = positive-degree-below-zero states). -/
theorem gradingZA_positivity (k : ℂ) (n : ℤ) (hn : n < 0) : gradingZA k n = ⊥ := by
  rw [gradingZA_def]
  refine eigenspace_eq_bot_of_not_energy kappaForm kappaForm_isInvariant k (-(n : ℂ)) ?_
  intro d hd
  -- `-(n:ℂ) = -(d:ℂ)` forces `n = d ≥ 0`, contradicting `n < 0`.
  have : (n : ℂ) = (d : ℂ) := by rw [neg_inj] at hd; exact hd
  have : n = (d : ℤ) := by exact_mod_cast this
  omega

/-! ## §B  The current fields are `IsField` (regularity / lower-truncation)

For the `nprod`/`dong_neg`/`goddard_uniqueness` machine the current fields `Jfield k a`
must be **fields**: lower-truncated on every state.  Via `Jfield k a j = J k a (-j-1)` this
is the regularity statement *high positive current modes annihilate every state*, which we
derive from the energy grading: `J^a_m` shifts the `ℓ₀`-energy by `-m` (it lands in degree
`(energy) - m`), and degrees below `0` vanish (`gradingZA_positivity`). -/

/-- **The energy shift of a current mode.**  `ell0Op (J^a_m v) = (m - energy(v))·(J^a_m v)`
when `v` is an `ell0Op`-eigenvector: `J^a_m` lowers the energy by `m`.  Stated as the
operator commutator `⁅ell0Op, J^a_m⁆ = m • J^a_m`. -/
theorem ell0Op_comm_J (k : ℂ) (a : Fin 3) (m : ℤ) (v : WakModule k) :
    ell0OpA k (J k a m v) = J k a m (ell0OpA k v) + (m : ℂ) • J k a m v := by
  rw [ell0OpA, ell0Op, J]
  rw [vacuumRho_comm kappaForm kappaForm_isInvariant k (ell0 kappaForm kappaForm_isInvariant)
    (ofLoop kappaForm kappaForm_isInvariant (basis a) m) v]
  rw [ell0_lie_ofLoop, map_smul, LinearMap.smul_apply]

/-- A current mode maps the energy-`n` (degree-`n`) piece into the degree-`(n-m)` piece:
`J^a_m : gradingZA k n → gradingZA k (n - m)` (the VA1 mode-grading, restricted to currents). -/
theorem J_mem_gradingZA (k : ℂ) (a : Fin 3) (m n : ℤ) {v : WakModule k}
    (hv : v ∈ gradingZA k n) : J k a m v ∈ gradingZA k (n - m) := by
  rw [gradingZA_def, Module.End.mem_eigenspace_iff] at hv ⊢
  rw [ell0Op_comm_J, hv, map_smul]
  push_cast
  module

/-- **Regularity on graded pieces**: a current mode `J^a_m` with `m > n` annihilates the
energy-`n` piece (it would land in negative degree `n - m < 0`, which is `⊥`). -/
theorem J_gradingZA_eq_zero (k : ℂ) (a : Fin 3) {m n : ℤ} (hmn : n < m) {v : WakModule k}
    (hv : v ∈ gradingZA k n) : J k a m v = 0 := by
  have hmem : J k a m v ∈ gradingZA k (n - m) := J_mem_gradingZA k a m n hv
  rw [gradingZA_positivity k (n - m) (by omega), Submodule.mem_bot] at hmem
  exact hmem

/-- **Regularity for an arbitrary state**: for every `x : WakModule k` there is a bound `B`
with `J^a_m x = 0` for all `m ≥ B`.  Decompose `x` into finitely many graded pieces (the
internal direct sum is supported on finitely many degrees) and take `B` above the top one. -/
theorem J_regularity (k : ℂ) (a : Fin 3) (x : WakModule k) :
    ∃ B : ℤ, ∀ m : ℤ, B ≤ m → J k a m x = 0 := by
  classical
  -- Decompose `x` along the internal direct sum `gradingZA` (surjectivity of `coeAddMonoidHom`).
  obtain ⟨c, rfl⟩ := (gradingZA_isInternal k).2 x
  -- `c : ⨁ n, gradingZA k n`; its support is a finite set of degrees, bounded above.
  obtain ⟨D, hD⟩ := Finset.exists_le c.support
  refine ⟨D + 1, fun m hm => ?_⟩
  rw [DirectSum.coeAddMonoidHom_eq_dfinsuppSum, DFinsupp.sum, map_sum]
  refine Finset.sum_eq_zero fun n hn => ?_
  exact J_gradingZA_eq_zero k a (by have := hD n hn; omega : n < m) (c n).2

/-- **The current field is a field** (`IsField`): lower-truncated on every state.  Via
`Jfield k a j = J k a (-j-1)`, low `j` means high positive mode `-j-1`, killed by
regularity.  This is the VA5-regularity input that lets `Jfield k a` enter the
`nprod`/`dong_neg` reconstruction machine. -/
theorem Jfield_isField (k : ℂ) (a : Fin 3) : IsField (Jfield k a) := by
  intro x
  obtain ⟨B, hB⟩ := J_regularity k a x
  refine ⟨-B, fun j hj => ?_⟩
  rw [Jfield_apply]
  exact hB (-j - 1) (by omega)

/-! ## §B′  Generator fields and the iterated normal-ordered product (the recipe)

The module-polymorphic Heisenberg recipe, ported to the affine currents:
`genFieldA k a i := (i!)⁻¹ ∂_z^i J^a(z)` (the field `Y(J^a_{-i-1}|0⟩, z)`), the identity
field `idFieldA = Y(|0⟩, z)`, and the iterated normal product `YwordA` over a creation
word (a `List (Fin 3 × ℕ)`).  All are `IsField` (so they enter `nprod`) and pairwise local
(`Jfield_local` ⟹ `dong_neg` cascade). -/

/-- The **scaled generator field** `genFieldA k a i := (i!)⁻¹ · ∂_z^i J^a(z)` — in the
vertex indexing exactly `Y(J^a_{-i-1}|0⟩, z)` (Gannon 5.2.5). -/
noncomputable def genFieldA (k : ℂ) (a : Fin 3) (i : ℕ) :
    FormalDist (End ℂ (WakModule k)) :=
  (i.factorial : ℂ)⁻¹ • (VOA.deriv^[i] (Jfield k a))

theorem genFieldA_isField (k : ℂ) (a : Fin 3) (i : ℕ) : IsField (genFieldA k a i) := by
  intro x
  obtain ⟨B, hB⟩ := (Jfield_isField k a).deriv_iterate i x
  exact ⟨B, fun n hn => by
    show ((i.factorial : ℂ)⁻¹ • (VOA.deriv^[i] (Jfield k a)) n) x = 0
    rw [LinearMap.smul_apply, hB n hn, smul_zero]⟩

theorem genFieldA_zero (k : ℂ) (a : Fin 3) : genFieldA k a 0 = Jfield k a := by
  rw [genFieldA, Function.iterate_zero, id, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul]

/-- The **identity field** `Y(|0⟩,z) = id`. -/
noncomputable def idFieldA (k : ℂ) : FormalDist (End ℂ (WakModule k)) :=
  fun j => if j = 0 then LinearMap.id else 0

theorem idFieldA_isField (k : ℂ) : IsField (idFieldA k) :=
  fun x => ⟨0, fun n hn => by rw [idFieldA, if_neg (by omega)]; rfl⟩

/-- The iterated normal-ordered product over a creation word `(a,i) :: …`, paired with its
field witness: `[]` ↦ the identity field; `(a,i) :: rest` ↦ `:(genFieldA a i)(YwordA rest):`. -/
noncomputable def YwordAF (k : ℂ) :
    List (Fin 3 × ℕ) → { f : FormalDist (End ℂ (WakModule k)) // IsField f }
  | [] => ⟨idFieldA k, idFieldA_isField k⟩
  | (ai :: rest) =>
      let p := YwordAF k rest
      ⟨nprod (genFieldA_isField k ai.1 ai.2) p.2,
        IsField.nprod (genFieldA_isField k ai.1 ai.2) p.2⟩

/-- The iterated normal-ordered product `YwordA k [(a₁,i₁),…] = :(∂^{i₁}J^{a₁}/i₁!)⋯:`. -/
noncomputable def YwordA (k : ℂ) (l : List (Fin 3 × ℕ)) :
    FormalDist (End ℂ (WakModule k)) := (YwordAF k l).1

theorem YwordA_isField (k : ℂ) (l : List (Fin 3 × ℕ)) : IsField (YwordA k l) :=
  (YwordAF k l).2

@[simp] theorem YwordA_nil (k : ℂ) : YwordA k [] = idFieldA k := rfl

theorem YwordA_cons (k : ℂ) (ai : Fin 3 × ℕ) (rest : List (Fin 3 × ℕ)) :
    YwordA k (ai :: rest)
      = nprod (genFieldA_isField k ai.1 ai.2) (YwordA_isField k rest) := rfl

/-! ## §B″  The word-field locality cascade (VA4 reduction toward reconstruction)

Every two iterated word fields are mutually local — the VA4 datum the reconstruction theorem
needs on the generating fields.  Proved by the same iterated `dong_neg` cascade as the free
boson (`Examples.HeisenbergNVertex`): the current-field locality `Jfield_local` lifts to the
scaled generators `genFieldA` (derivative locality + scalar), then to words by induction. -/

/-- Iterated derivatives of the current fields are mutually local. -/
theorem dJfield_local (k : ℂ) (a b : Fin 3) (i j : ℕ) :
    Local (VOA.deriv^[i] (Jfield k a)) (VOA.deriv^[j] (Jfield k b)) :=
  ((Jfield_local k a b).deriv_iterate_left i).deriv_iterate_right j

/-- The scaled generator fields `genFieldA k a i = (i!)⁻¹ ∂_z^i J^a(z)` are mutually local. -/
theorem genFieldA_local (k : ℂ) (a b : Fin 3) (i j : ℕ) :
    Local (genFieldA k a i) (genFieldA k b j) := by
  change Local ((i.factorial : ℂ)⁻¹ • (VOA.deriv^[i] (Jfield k a)))
    ((j.factorial : ℂ)⁻¹ • (VOA.deriv^[j] (Jfield k b)))
  exact Local.smulR _ (VertexOperatorAlgebra.Local.smul' _ (dJfield_local k a b i j))

/-- The identity field commutes with every distribution: `[1(z₁), b(z₂)] = 0`. -/
theorem bracketDist_idFieldA_left (k : ℂ) (b : FormalDist (End ℂ (WakModule k))) :
    bracketDist (idFieldA k) b = 0 := by
  apply FormalDist₂.ext; intro m n
  rw [bracketDist_apply, idFieldA]
  change (if m = 0 then LinearMap.id else 0 : End ℂ (WakModule k)) * b n
      - b n * (if m = 0 then LinearMap.id else 0) = (0 : FormalDist₂ (End ℂ (WakModule k))) m n
  by_cases h : m = 0
  · rw [if_pos h, show (LinearMap.id : End ℂ (WakModule k)) = 1 from rfl, one_mul, mul_one, sub_self]
    rfl
  · rw [if_neg h, zero_mul, mul_zero, sub_zero]; rfl

theorem Local_idFieldA_left (k : ℂ) (b : FormalDist (End ℂ (WakModule k))) :
    Local (idFieldA k) b :=
  local_of_bracketDist_eq_zero (bracketDist_idFieldA_left k b)

theorem Local_idFieldA_right (k : ℂ) (b : FormalDist (End ℂ (WakModule k))) :
    Local b (idFieldA k) :=
  (Local_idFieldA_left k b).symm

/-- Each generator field is local with every iterated word field (induction on the word). -/
theorem genFieldA_local_YwordA (k : ℂ) :
    ∀ (l : List (Fin 3 × ℕ)) (i : ℕ) (a : Fin 3),
      Local (genFieldA k a i) (YwordA k l) := by
  intro l
  induction l with
  | nil => intro i a; rw [YwordA_nil]; exact Local_idFieldA_right k _
  | cons ai rest ih =>
      intro i a
      have hab : Local (genFieldA k ai.1 ai.2) (YwordA k rest) := ih ai.2 ai.1
      have hac : Local (genFieldA k ai.1 ai.2) (genFieldA k a i) :=
        genFieldA_local k ai.1 a ai.2 i
      have hbc : Local (YwordA k rest) (genFieldA k a i) := (ih i a).symm
      have hmain : Local (nprod (genFieldA_isField k ai.1 ai.2) (YwordA_isField k rest))
          (genFieldA k a i) :=
        dong_neg (genFieldA_isField k ai.1 ai.2) (YwordA_isField k rest) hab hac hbc
      rw [YwordA_cons]
      exact hmain.symm

/-- **VA4 reduction** (Gannon 5.2.5c): every two iterated word fields are mutually local — the
locality datum on the generating fields that the reconstruction theorem consumes. -/
theorem YwordA_local (k : ℂ) :
    ∀ (l₁ l₂ : List (Fin 3 × ℕ)), Local (YwordA k l₁) (YwordA k l₂) := by
  intro l₁
  induction l₁ with
  | nil => intro l₂; rw [YwordA_nil]; exact Local_idFieldA_left k _
  | cons ai rest ih =>
      intro l₂
      have hab : Local (genFieldA k ai.1 ai.2) (YwordA k rest) :=
        genFieldA_local_YwordA k rest ai.2 ai.1
      have hac : Local (genFieldA k ai.1 ai.2) (YwordA k l₂) :=
        genFieldA_local_YwordA k l₂ ai.2 ai.1
      have hbc : Local (YwordA k rest) (YwordA k l₂) := ih l₂
      have hmain : Local (nprod (genFieldA_isField k ai.1 ai.2) (YwordA_isField k rest))
          (YwordA k l₂) :=
        dong_neg (genFieldA_isField k ai.1 ai.2) (YwordA_isField k rest) hab hac hbc
      rw [YwordA_cons]
      exact hmain

/-! ## §B‴  The creation tower of the word fields (STEP 2 of reconstruction)

Each iterated word field `YwordA k l` *creates* its word-state from the vacuum as a power series:
`(YwordA k l)_0 |0⟩ = wordStateA l` (the creation word) and `(YwordA k l)_q |0⟩ = 0` for `q < 0`.
Together with `YwordA_local` this pins each word field by its created state (the data the
reconstruction `YA` is defined from).  Built on the generic `nprod_vacuum_{base,neg}_gen`
(`Core.Dong`) + the highest-weight condition `vacuum_pos_annihilate`. -/

/-- Positive current modes annihilate the vacuum: `J^a_m |0⟩ = 0` for `m ≥ 0`. -/
theorem J_vacuum_nonneg (k : ℂ) (a : Fin 3) {m : ℤ} (hm : 0 ≤ m) : J k a m (vacuumA k) = 0 :=
  vacuum_pos_annihilate kappaForm kappaForm_isInvariant k (basis a) m hm

/-- The current field annihilates the vacuum below degree `0`. -/
theorem Jfield_vacuum_neg (k : ℂ) (a : Fin 3) {q : ℤ} (hq : q < 0) :
    Jfield k a q (vacuumA k) = 0 := by
  rw [Jfield_apply]; exact J_vacuum_nonneg k a (by omega)

/-- The generator field annihilates the vacuum below degree `0` (a power series on `|0⟩`). -/
theorem genFieldA_vacuum_neg (k : ℂ) (a : Fin 3) (i : ℕ) {q : ℤ} (hq : q < 0) :
    genFieldA k a i q (vacuumA k) = 0 := by
  show ((i.factorial : ℂ)⁻¹ • (VOA.deriv^[i] (Jfield k a)) q) (vacuumA k) = 0
  rw [VertexOperatorAlgebra.deriv_pow_apply,
    ← Int.cast_smul_eq_zsmul ℂ (∏ m ∈ Finset.range i, (q + 1 + (m : ℤ)))]
  simp only [LinearMap.smul_apply]
  by_cases hqi : q + (i : ℤ) < 0
  · rw [Jfield_vacuum_neg k a (show q + (i : ℤ) < 0 by omega), smul_zero, smul_zero]
  · rw [Finset.prod_eq_zero (i := (-q - 1).toNat) (Finset.mem_range.mpr (by omega))
        (by rw [show ((-q - 1).toNat : ℤ) = -q - 1 from by omega]; ring),
      Int.cast_zero, zero_smul, smul_zero]

/-- The generator field's `z⁰`-coefficient is the creation mode: `(genFieldA k a i)₀ = J^a_{-i-1}`. -/
theorem genFieldA_zero_op (k : ℂ) (a : Fin 3) (i : ℕ) :
    (genFieldA k a i) 0 = J k a (-(i : ℤ) - 1) := by
  show (i.factorial : ℂ)⁻¹ • ((VOA.deriv^[i] (Jfield k a)) 0) = _
  rw [VertexOperatorAlgebra.deriv_pow_apply,
    show (∏ m ∈ Finset.range i, ((0 : ℤ) + 1 + (m : ℤ))) = (i.factorial : ℤ) from by
        rw [← VertexOperatorAlgebra.prod_one_add_factorial]
        exact Finset.prod_congr rfl (fun m _ => by ring),
    ← Int.cast_smul_eq_zsmul ℂ (i.factorial : ℤ), Int.cast_natCast, smul_smul,
    inv_mul_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero i), one_smul,
    show (0 : ℤ) + (i : ℤ) = (i : ℤ) from by ring, Jfield_apply]

/-- The **word-state map**: the creation word applied to the vacuum (matching `negWord`). -/
noncomputable def wordStateA (k : ℂ) : List (Fin 3 × ℕ) → WakModule k
  | [] => vacuumA k
  | (ai :: rest) => J k ai.1 (-(ai.2 : ℤ) - 1) (wordStateA k rest)

@[simp] theorem wordStateA_nil (k : ℂ) : wordStateA k [] = vacuumA k := rfl

theorem wordStateA_cons (k : ℂ) (ai : Fin 3 × ℕ) (rest : List (Fin 3 × ℕ)) :
    wordStateA k (ai :: rest) = J k ai.1 (-(ai.2 : ℤ) - 1) (wordStateA k rest) := rfl

/-- **Creation tower (power-series part)**: `(YwordA k l)_q |0⟩ = 0` for `q < 0`. -/
theorem YwordA_vacuum_neg (k : ℂ) (l : List (Fin 3 × ℕ)) :
    ∀ {q : ℤ}, q < 0 → (YwordA k l) q (vacuumA k) = 0 := by
  induction l with
  | nil =>
      intro q hq
      rw [YwordA_nil]
      show (if q = 0 then (LinearMap.id : End ℂ (WakModule k)) else 0) (vacuumA k) = 0
      rw [if_neg (by omega : ¬ q = 0)]; rfl
  | cons ai rest ih =>
      intro q hq
      rw [YwordA_cons]
      exact nprod_vacuum_neg_gen (genFieldA_isField k ai.1 ai.2) (YwordA_isField k rest)
        (vacuumA k) (fun s hs => genFieldA_vacuum_neg k ai.1 ai.2 hs) (fun s hs => ih hs) hq

/-- **Creation tower (base)**: `(YwordA k l)_0 |0⟩ = wordStateA l` — the field creates the
word-state from the vacuum. -/
theorem YwordA_vacuum_base (k : ℂ) (l : List (Fin 3 × ℕ)) :
    (YwordA k l) 0 (vacuumA k) = wordStateA k l := by
  induction l with
  | nil =>
      rw [YwordA_nil]
      show (if (0 : ℤ) = 0 then (LinearMap.id : End ℂ (WakModule k)) else 0) (vacuumA k)
        = wordStateA k []
      rw [if_pos rfl]; rfl
  | cons ai rest ih =>
      rw [YwordA_cons,
        nprod_vacuum_base_gen (genFieldA_isField k ai.1 ai.2) (YwordA_isField k rest)
          (vacuumA k) (fun s hs => genFieldA_vacuum_neg k ai.1 ai.2 hs)
          (fun s hs => YwordA_vacuum_neg k rest hs),
        genFieldA_zero_op, ih, wordStateA_cons]

/-! ## §C  The Sugawara conformal vector and the central charge `c = 3k/(k+2)`

`T(z) = (1/(2(k+2))) ∑_{a,b} κ⁻¹(a,b) :J^a(z) J^b(z):` with the inverse Killing form
`κ⁻¹` of `𝔰𝔩₂` (`κ(e,f)=1`, `κ(h,h)=2` ⟹ `κ⁻¹(e,f)=1`, `κ⁻¹(h,h)=1/2`).  The dual
Coxeter number is `h^∨ = 2` and `dim 𝔰𝔩₂ = 3`, giving the central charge
`c = k·dim/(k+h^∨) = 3k/(k+2)` (Gannon §5.2.2, eq. 5.2.6). -/

/-- The **inverse normalised Killing form** `κ⁻¹` of `𝔰𝔩₂` (Chevalley basis):
`κ⁻¹(e,f)=κ⁻¹(f,e)=1`, `κ⁻¹(h,h)=1/2`, else `0`. -/
noncomputable def kappaInv : Fin 3 → Fin 3 → ℂ
  | 0, 1 => 1
  | 1, 0 => 1
  | 2, 2 => 1/2
  | _, _ => 0

/-- `κ⁻¹` is symmetric. -/
theorem kappaInv_symm (a b : Fin 3) : kappaInv a b = kappaInv b a := by
  fin_cases a <;> fin_cases b <;> simp [kappaInv]

/-- `κ⁻¹` inverts `κ`: `∑_b κ(a,b)·κ⁻¹(b,c) = δ_{a,c}` — the defining identity used in the
Sugawara/Virasoro computation (Casimir normalisation).  A `Fin 3` bash. -/
theorem kappaInv_kappa (a c : Fin 3) :
    (∑ b, kappa a b * kappaInv b c) = if a = c then 1 else 0 := by
  fin_cases a <;> fin_cases c <;>
    norm_num [Fin.sum_univ_three, kappa, kappaInv]

/-- The dual Coxeter number of `𝔰𝔩₂` (`h^∨ = 2`), an explicit number. -/
def dualCoxeter : ℂ := 2

/-- `dim 𝔰𝔩₂ = 3`, an explicit number. -/
def dimSl2 : ℂ := 3

/-- **The Sugawara field** `T(z) = (1/(2(k+2))) ∑_{a,b} κ⁻¹(a,b) :J^a(z) J^b(z):`
(Gannon §5.2.2, eq. 5.2.6).  Each `:J^a J^b:` is `nprod (Jfield a) (Jfield b)`; the prefactor
`1/(2(k+h^∨)) = 1/(2(k+2))`. -/
noncomputable def sugawaraField (k : ℂ) : FormalDist (End ℂ (WakModule k)) :=
  (2 * (k + dualCoxeter))⁻¹ •
    ∑ a : Fin 3, ∑ b : Fin 3,
      kappaInv a b • nprod (Jfield_isField k a) (Jfield_isField k b)

/-- A scalar multiple of a field is a field. -/
theorem IsField.smulC {k : ℂ} {f : FormalDist (End ℂ (WakModule k))} (hf : IsField f)
    (c : ℂ) : IsField (c • f) := by
  intro x
  obtain ⟨B, hB⟩ := hf x
  exact ⟨B, fun n hn => by
    show (c • f n) x = 0
    rw [LinearMap.smul_apply, hB n hn, smul_zero]⟩

/-- A finite sum of fields is a field (uniform lower-truncation bound over the finite index). -/
theorem IsField.finsetSum {k : ℂ} {ι : Type*} (s : Finset ι)
    (F : ι → FormalDist (End ℂ (WakModule k))) (hF : ∀ i ∈ s, IsField (F i)) :
    IsField (∑ i ∈ s, F i) := by
  classical
  intro x
  induction s using Finset.induction with
  | empty => exact ⟨0, fun n _ => by rw [Finset.sum_empty]; rfl⟩
  | insert i s hi ih =>
      obtain ⟨B₁, hB₁⟩ := hF i (Finset.mem_insert_self i s) x
      obtain ⟨B₂, hB₂⟩ := ih (fun j hj => hF j (Finset.mem_insert_of_mem hj))
      refine ⟨min B₁ B₂, fun n hn => ?_⟩
      rw [Finset.sum_insert hi]
      show (F i n + (∑ j ∈ s, F j) n) x = 0
      rw [LinearMap.add_apply, hB₁ n (by omega), hB₂ n (by omega), add_zero]

/-- The Sugawara field is a field (`IsField`): a finite ℂ-combination of `nprod`s of fields. -/
theorem sugawaraField_isField (k : ℂ) : IsField (sugawaraField k) := by
  rw [sugawaraField]
  refine IsField.smulC ?_ _
  refine IsField.finsetSum _ _ fun a _ => ?_
  refine IsField.finsetSum _ _ fun b _ => ?_
  exact IsField.smulC (IsField.nprod (Jfield_isField k a) (Jfield_isField k b)) _

/-- **The Sugawara modes** `Lₙ := mode (T) (n+1) = T₍ₙ₊₁₎` (the conformal-weight-`2` shift,
`CONVENTIONS` §5), endomorphisms of `WakModule k`. -/
noncomputable def Lsug (k : ℂ) (n : ℤ) : End ℂ (WakModule k) :=
  mode (sugawaraField k) (n + 1)

theorem Lsug_def (k : ℂ) (n : ℤ) : Lsug k n = mode (sugawaraField k) (n + 1) := rfl

/-- **The conformal vector** `ω = L₋₂|0⟩`, the weight-`2` Sugawara state.  In the field
indexing `Lsug k (-2) = mode T (-1) = T₀`, so `ω = (sugawaraField k) 0 |0⟩` — the constant
term of `T(z)|0⟩`, the state created by the Sugawara field (Gannon §5.2.2). -/
noncomputable def omegaA (k : ℂ) : WakModule k := Lsug k (-2) (vacuumA k)

theorem omegaA_eq (k : ℂ) : omegaA k = (sugawaraField k) 0 (vacuumA k) := by
  rw [omegaA, Lsug_def, mode_apply, show -(-2 + 1) - 1 = (0 : ℤ) from by ring]

/-! ### The central charge `c = 3k/(k+2)` -/

/-- The **central charge** of the affine `𝔰𝔩₂` VOA at level `k`:
`c = k·dim 𝔤 / (k + h^∨) = 3k/(k+2)` (Gannon §5.2.2, eq. 5.2.6). -/
noncomputable def centralChargeA (k : ℂ) : ℂ := dimSl2 * k / (k + dualCoxeter)

/-- The central-charge value spelled out: `c = 3k/(k+2)` (using `dim 𝔰𝔩₂ = 3`, `h^∨ = 2`). -/
theorem centralChargeA_eq (k : ℂ) : centralChargeA k = 3 * k / (k + 2) := by
  rw [centralChargeA, dimSl2, dualCoxeter]

/-! ## §D  The instance shell and the isolated `YA` obstruction

The grading (`gradingZA_isInternal`, `gradingZA_finiteDimensional`), the vacuum data
(`vacuumA_mem_gradingZA_zero`, `gradingZA_zero_eq_smul_vacuum`, `gradingZA_positivity`),
regularity (`J_regularity`), locality of the generating currents (`Jfield_local`), and the
conformal datum (`omegaA`, `centralChargeA = 3k/(k+2)`) are all proved axiom-cleanly above.

The single missing ingredient is the **all-states vertex map**
`YA : WakModule k →ₗ[ℂ] FormalDist (End ℂ (WakModule k))` extending the generating fields,
together with its `YA`-dependent VA/VOA axioms (VA1 mode-grading, VA2 `YA |0⟩ = id`, VA3
creation, VA4 locality, VA5 regularity, and VOA1–3).  The Heisenberg recipe builds the
analogous `YN` as `Finsupp.linearCombination ℂ (YmonN r k)` over the free monomial basis of
`FockN r = MvPolynomial (ℕ × Fin r) ℂ`.  `WakModule k = U(ĝ)⧸J(k)` carries no free
`Finsupp` basis here (`VOA.pbw` supplies only `|0⟩ ≠ 0`; the full PBW basis was proved later,
`VOA.pbwBasis_holds`, and is not used in this file), so `YA` is not assembled by
`linearCombination`.  We therefore
package the instance as a constructor consuming `YA` and its axioms, discharging every
basis-independent field; closing it needs the module-polymorphic *reconstruction theorem*
(build `Y` on a cyclic module from generating local fields). -/

/-- **The instance shell.**  Given the all-states vertex map `YA` and its `YA`-dependent
VA/VOA axioms (the basis-free reconstruction data), the affine `𝔰𝔩₂` VOA `𝒱(𝔰𝔩₂, k)` at
level `k` (with `k + 2 ≠ 0`) is assembled: the grading, finite-dimensional pieces, vacuum,
CFT-type, conformal vector `ω = omegaA k`, and central charge `c = 3k/(k+2)` are all the
proved data of this file.  Only the seven `YA`-fields are hypotheses (the isolated
obstruction). -/
noncomputable def affineSl2VOA (k : ℂ) (_hk : k + 2 ≠ 0)
    (YA : WakModule k →ₗ[ℂ] FormalDist (End ℂ (WakModule k)))
    (hYA_vac : YA (vacuumA k) = (1 : (End ℂ (WakModule k))⟦z^±⟧))
    (hYA_grading : ∀ {p q : ℤ} (u : WakModule k), u ∈ gradingZA k p →
        ∀ (v : WakModule k), v ∈ gradingZA k q → ∀ (n : ℤ),
        mode (YA u) n v ∈ gradingZA k (p + q - n - 1))
    (hYA_creation : ∀ u : WakModule k,
        mode (YA u) (-1) (vacuumA k) = u ∧
          ∀ n : ℤ, 0 ≤ n → mode (YA u) n (vacuumA k) = 0)
    (hYA_local : ∀ u v : WakModule k, Local (YA u) (YA v))
    (hYA_reg : ∀ u v : WakModule k, ∃ N : ℤ, ∀ n : ℤ, N ≤ n → mode (YA u) n v = 0)
    (hYA_omega_mem : omegaA k ∈ gradingZA k 2)
    (hYA_virasoro : ∀ m n : ℤ,
        ⁅mode (YA (omegaA k)) (m + 1), mode (YA (omegaA k)) (n + 1)⁆
          = ((m : ℂ) - n) • mode (YA (omegaA k)) (m + n + 1)
            + (if m + n = 0 then
                (((m : ℂ) ^ 3 - m) / 12 * centralChargeA k) • (1 : End ℂ (WakModule k))
               else 0))
    (hYA_L0 : ∀ {n : ℤ} (v : WakModule k), v ∈ gradingZA k n →
        mode (YA (omegaA k)) 1 v = (n : ℂ) • v)
    (hYA_translation : ∀ v : WakModule k,
        YA (mode (YA (omegaA k)) 0 v) = deriv (YA v)) :
    VertexOperatorAlgebra (WakModule k) where
  grading := gradingZA k
  isInternal := gradingZA_isInternal k
  finrank := gradingZA_finiteDimensional k
  Y := YA
  vacuum := vacuumA k
  vacuum_mem := vacuumA_mem_gradingZA_zero k
  grading_mode := fun u hu v hv n => hYA_grading u hu v hv n
  vacuum_Y := hYA_vac
  creation := hYA_creation
  locality := hYA_local
  regularity := hYA_reg
  conformalVector := omegaA k
  conformal_mem := hYA_omega_mem
  centralCharge := centralChargeA k
  virasoro := hYA_virasoro
  L0_grading := fun v hv => hYA_L0 v hv
  translation := hYA_translation
  vacuum_grade := gradingZA_zero_eq_smul_vacuum k
  positivity := fun n hn => gradingZA_positivity k n hn

/-- **The central charge of the affine `𝔰𝔩₂` VOA is `3k/(k+2)`** (Gannon §5.2.2): on the
assembled instance the `centralCharge` field is `centralChargeA k = 3k/(k+2)`. -/
theorem affineSl2_central_charge (k : ℂ) (hk : k + 2 ≠ 0)
    (YA : WakModule k →ₗ[ℂ] FormalDist (End ℂ (WakModule k)))
    (h1 _ _ _ _ _ _ _ _ : _) :
    (affineSl2VOA k hk YA h1 ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).centralCharge
      = 3 * k / (k + 2) :=
  centralChargeA_eq k

/-! ## §E  Axiom audit

The current-algebra layer (regularity, `IsField` of the currents, the grading) uses
`VOA.pbw` through `WakModule` nonvanishing;
everything is `sorry`-free and uses only Lean's three standard axioms. -/

-- pbw (a theorem) used via `vacuumA_ne_zero` / the `ell0`-grading on the nonzero `WakModule`:
-- the basis-free toolkit pieces are clean (propext/Classical.choice/Quot.sound only):

end VOA.AffineVOA
