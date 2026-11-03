/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modularity.BlockGrowth
import VOA.Modules.PoissonTrace
import VOA.Examples.ZhuInstantiation

/-!
# Arakawa–Kawasetsu §5 from the Etingof–Schedler finiteness hypothesis

Zhu's modularity theorem assumes `C₂`-cofiniteness, `dim_ℂ A₂(𝒱) < ∞` where
`A₂(𝒱) = R_V = 𝒱 ⧸ O₂(𝒱)`.  Arakawa–Kawasetsu (*Quasi-lisse vertex algebras and modular linear
differential equations*, arXiv:1610.05865; Progr. Math. **326** (2018)) observe that the finite
generation which drives Zhu's argument needs only the **weaker** hypothesis

  `dim_ℂ R_V ⧸ {R_V, R_V} < ∞`,

which by Etingof–Schedler (*Poisson traces and D-modules on Poisson varieties*, GAFA **20** (2010)
958–987) holds whenever `𝒱` is **quasi-lisse** — the associated variety `X_𝒱` has finitely many
symplectic leaves.  `Modules.PoissonTrace` records that conclusion as the hypothesis
`EtingofFinite W`.  This file carries it through Zhu's finite-generation argument.

The mechanism, in one line: Zhu's relation space already contains the generators `a[0]v` and his
proof never used them; modulo lower conformal weight `a[0]v` **is** the Poisson bracket `a₍₀₎v`, so
the relation space contains representatives of `{R_V, R_V}` for free (`vSqZ_zero_eq`,
`brk_mem_pullbackG`).

## Main results

* `etingofFinite_iff_quot_O₂P` — **AK Thm 2.2, read upstairs**:
  `EtingofFinite W ↔ dim_ℂ (𝒱 ⧸ (O₂ 𝒱 + span{u₍₀₎v})) < ∞`.  The subspace is `O₂P W`;
  `map_mkQ_O₂P` identifies its image in `A₂(𝒱)` with `poissonSpan W = {R_V, R_V}`;
* `O₂P_eq_span_O₂PhomGen`, `piHom_maps_O₂P`, `grading_le_span_sup_O₂P_inf`,
  `O₂P_inf_grading_le_span_deg` — `O₂P` is a **graded** subspace, so the repository's downward
  degree induction applies to it;
* `vSqZ_zero_eq`, `sqDefect0_mem_of_lower` — **mode-`0` triangularity**: `a[0]b = a₍₀₎b + (terms
  of strictly lower conformal weight)`.  This is AK's "pass to `gr` by conformal weight", realized
  without constructing an associated-graded object;
* `brk_mem_pullbackG` — the new induction branch, the bracket analogue of
  `vSqZ_negTwo_mem_of_blockRelSpanG`.  It is *easier* than the `₍₋₂₎` branch: the `a[0]`-relation
  is exact, with no Eisenstein tail;
* `grading_le_pullbackG_of_poisson`, `span_sup_blockRelSpanG_eq_top_of_poisson` — the ported
  degree induction and its span form;
* `exists_finset_span_sup_of_quot_finite`, `exists_homog_gen_of_quot_finite`,
  `exists_homog_gen_of_etingofFinite` — the spanning datum from `EtingofFinite`;
* `exists_finite_gen_sup_blockRelSpanG_of_etingofFinite` — **AK Proposition 5.2**:
  `V_A ⧸ ([V_A,V_A] + O_q(V))` is a finitely generated `A`-module, `A = ℂ[G₂,G₄,G₆]`.  Identical
  conclusion to `Modularity.BlockRelSpanG.moduleFinite_quot_blockRelSpanG`, weaker hypothesis;
* `fg_blockSpan_of_etingofFinite`, `fg_blockSpanS_of_fg`, `exists_system_matrix_of_fg`,
  `subexponential_block_of_fg`, `subexponential_block_of_etingofFinite`;
* `onePointSubexp_of_etingofFinite` — `Modularity.BlockGrowth.onePointSubexp_of_c2` with
  `C2Cofinite` weakened to `EtingofFinite`;
* `trivial_etingofFinite`, `trivial_exists_finite_gen_sup_blockRelSpanG`,
  `trivial_onePointSubexp_adjoint` — a witness, so nothing above is vacuous;
* `span_sup_O₂P_eq_top_of_span_sup_O₂`, `onePointSubexp_of_c2_via_etingofFinite` — the consistency
  checks: the new hypothesis is implied by the old one, and the new conclusion recovers the old.

## ⚠ What is assumed, and what is *not* claimed

**`EtingofFinite` is a deliberate axiomatization of the conclusion of an external theorem, not a
proof of it.**  Etingof–Schedler prove that a finitely generated Poisson algebra whose variety has
finitely many symplectic leaves has finite-dimensional zeroth Poisson homology; AK apply this to
`R_V` under quasi-lisseness.  Symplectic leaves, associated varieties and the D-module machinery of
Etingof–Schedler are **not formalized anywhere in this repository**, and **quasi-lisseness itself is
not defined here**.  Every statement below is either a proof *from* `EtingofFinite W` as an explicit
named hypothesis, or a proof that `C₂`-cofiniteness implies it
(`Modules.PoissonTrace.EtingofFinite_of_C2Cofinite`).  Nothing here proves Etingof–Schedler, and
nothing here asserts that any particular VOA is quasi-lisse.

**No MLDE is proved here, and none is claimed.**  See the Status section.

## Status

Proved, `sorry`-free, axiom-clean (`propext`/`Classical.choice`/`Quot.sound` only), no use of the
theorem `VOA.pbw`.

**What closed.**  The *finiteness half* of Arakawa–Kawasetsu §5: Proposition 5.2 and everything
this repository derives from it, under `EtingofFinite` in place of `C2Cofinite`.  Concretely, the
chain `EtingofFinite → spanning datum → AK Prop 5.2 → finitely generated block span → first-order
system → subexponential growth → OnePointSubexp` is complete and unconditional given the
hypothesis.

⚠ **What did *not* close, in dependency order.**

1. **AK Lemma 5.3 and the monic `L[−2]`-relation are not derived *in this file*.**  This file's
   own route to the growth datum deliberately bypasses the scalar ODE, via
   `Modularity.BlockSystem`'s first-order **system** for a finite generating family.

   ⚠ **Correction.**  An earlier version of this note said that the per-vector unitriangular
   reading of Zhu Lemma 4.4.4 refuted by `Modularity.UniCollapse` "is AK Lemmas 5.4–5.6".  *That
   was wrong.*  Lemmas 5.4 and 5.6 are per-vector statements and are already theorems here
   (`Modularity.ZhuBlockConditions.zhuRecursion_omega`, `zhuRecursion_neg_two`,
   `torusOnePoint_vSqZ_zero_eq_zero`, packaged as `IsFormalBlock`).  Only **Lemma 5.5** carries the
   extra hypothesis that `a` be square-bracket **primary**, and `UniCollapse`'s refutation runs
   entirely through `v = L[−1]x`, which is *not* primary — so it is not an instance of Lemma 5.5.
   AK Lemmas 5.3 and 5.5, and AK equation (2) in scalar monic form, are proved in
   `Modularity.AKModularODE` (`exists_monic_Lsq_relation_of_etingofFinite`, `huni_of_sqPrimary`,
   `formalODE_of_etingofFinite_of_sqPrimary`), under `EtingofFinite` and for a primary vector.
2. **AK Theorem 5.7 / 5.1 (the MLDE) is still NOT proved.**  `Modularity.AKModularODE` delivers
   only the **formal** half of Theorem 5.7 — AK equation (2) as an identity of formal `q`-series,
   in the `(q d/dq)^i` basis and with *subexponential* coefficients rather than coefficients in
   `A = ℂ[G̃₄,G̃₆]`.  Nothing is proved there about modularity of the coefficients, about the
   analytic limit function `p_i(τ)`, or about the `ϑ_Δ` operators on `ℍ`.  And even granted all of
   that, AK's conclusion is only that characters are *among* the solutions of *some* modular linear
   differential equation — not that the span of characters is an `SL(2,ℤ)`-representation, nor that
   it is the full solution space.
3. **The modularity headline is unaffected.**  `Modularity.ZhuModularityFibre` uses `C2Cofinite` in
   a second, independent place (the block-space rank count,
   `rank_map_sqRestrict_analyticBlocks_le`), which this file does not touch.  Weakening the growth
   datum alone does not weaken `Modularity.ZhuModularityC2.exists_zhuModularity_of_c2`.
4. **An unconditional non-`C₂`-cofinite witness exists**: `L_{-4/3}(𝔰𝔩₂)` satisfies
   `EtingofFinite` (`Sl2Pres.etingofFinite_simpleSl2QL'`, `Examples/AffineSl2Presentation.lean`) and
   is not `C₂`-cofinite (`Sl2NonLisse.not_C2Cofinite_simpleSl2QL`,
   `Examples/AffineSl2NonLisse.lean`).  Quasi-lisseness itself is still not defined; see §7.

## References

* T. Arakawa, K. Kawasetsu, *Quasi-lisse vertex algebras and modular linear differential
  equations*, arXiv:1610.05865v4; in: Lie Groups, Geometry, and Representation Theory,
  Progr. Math. **326**, Birkhäuser (2018) 41–57.  §5, Prop. 5.2 and Thm 2.2.
* P. Etingof, T. Schedler, *Poisson traces and D-modules on Poisson varieties*,
  Geom. Funct. Anal. **20** (2010) 958–987, arXiv:0908.3868.
* Y. Zhu, *Modular invariance of characters of vertex operator algebras*, J. Amer. Math. Soc. **9**
  (1996) 237–302.  Lemmas 4.4.1, 4.4.2; relation (5.1).
* C. Dong, H. Li, G. Mason, *Modular-invariance of trace functions in orbifold theory and
  generalized Moonshine*, Comm. Math. Phys. **214** (2000) 1–56.  Lemma 5.2.
-/

namespace VOA

open scoped BigOperators TensorProduct

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

/-! ## §1  The augmented relation space `O₂(𝒱) + {𝒱, 𝒱}` -/

/-- The span **upstairs in `𝒱`** of the Poisson-bracket representatives `u₍₀₎v`.  Its image in
`A₂(𝒱)` is `poissonSpan W = {A₂, A₂}` (`map_mkQ_O₂P`). -/
noncomputable def poissonUp (W : VertexOperatorAlgebra 𝒱) : Submodule ℂ 𝒱 :=
  Submodule.span ℂ {x : 𝒱 | ∃ u v : 𝒱, x = poissonBracket W u v}

/-- **The augmented relation space** `O₂(𝒱) + span{u₍₀₎v}`.

In Arakawa–Kawasetsu's notation `R_V = A₂(𝒱) = 𝒱 ⧸ O₂(𝒱)` and `{R_V, R_V} = poissonSpan W`, so
`𝒱 ⧸ O₂P W ≅ R_V ⧸ {R_V, R_V} = HP₀(R_V)`; that identification is `etingofFinite_iff_quot_O₂P`. -/
noncomputable def O₂P (W : VertexOperatorAlgebra 𝒱) : Submodule ℂ 𝒱 := O₂ W ⊔ poissonUp W

theorem O₂_le_O₂P (W : VertexOperatorAlgebra 𝒱) : O₂ W ≤ O₂P W := le_sup_left

theorem poissonUp_le_O₂P (W : VertexOperatorAlgebra 𝒱) : poissonUp W ≤ O₂P W := le_sup_right

/-- `u₍₀₎v ∈ poissonUp W`. -/
theorem smul_zero_mem_poissonUp (W : VertexOperatorAlgebra 𝒱) (u v : 𝒱) :
    W.smul u 0 v ∈ poissonUp W :=
  Submodule.subset_span ⟨u, v, rfl⟩

/-- `u₍₀₎v ∈ O₂P W`. -/
theorem smul_zero_mem_O₂P (W : VertexOperatorAlgebra 𝒱) (u v : 𝒱) :
    W.smul u 0 v ∈ O₂P W :=
  poissonUp_le_O₂P W (smul_zero_mem_poissonUp W u v)

/-- `u₍₋₂₎v ∈ O₂P W`. -/
theorem smul_negTwo_mem_O₂P (W : VertexOperatorAlgebra 𝒱) (u v : 𝒱) :
    W.smul u (-2) v ∈ O₂P W :=
  O₂_le_O₂P W (Submodule.subset_span ⟨u, v, rfl⟩)

/-- The image of `O₂P` in `A₂(𝒱)` is exactly the bracket span `{A₂, A₂}`. -/
theorem map_mkQ_O₂P (W : VertexOperatorAlgebra 𝒱) :
    Submodule.map (O₂ W).mkQ (O₂P W) = poissonSpan W := by
  rw [O₂P, Submodule.map_sup, poissonUp, poissonSpan_eq_map, mk₂]
  have h : Submodule.map (O₂ W).mkQ (O₂ W) = ⊥ := by
    rw [eq_bot_iff]; rintro _ ⟨x, hx, rfl⟩
    simp only [Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hx
  rw [h, bot_sup_eq]

/-- **The Etingof–Schedler hypothesis, read upstairs in `𝒱`.**

`EtingofFinite W` says `dim_ℂ HP₀(R_V) = dim_ℂ R_V ⧸ {R_V, R_V} < ∞` — the conclusion Arakawa–
Kawasetsu quote as their Theorem 2.2 (from Etingof–Schedler, GAFA **20** (2010) 958–987).  Its
content upstairs is that the *single* subspace `O₂(𝒱) + span{u₍₀₎v} ⊆ 𝒱` has finite codimension.

That is the form the spanning machinery of this repository consumes: everything downstream needs a
finite family spanning `𝒱` modulo one explicit subspace, and this identifies which subspace. -/
theorem etingofFinite_iff_quot_O₂P (W : VertexOperatorAlgebra 𝒱) :
    EtingofFinite W ↔ FiniteDimensional ℂ (𝒱 ⧸ O₂P W) := by
  have e : ((𝒱 ⧸ O₂ W) ⧸ Submodule.map (O₂ W).mkQ (O₂P W)) ≃ₗ[ℂ] 𝒱 ⧸ O₂P W :=
    Submodule.quotientQuotientEquivQuotient (O₂ W) (O₂P W) le_sup_left
  rw [map_mkQ_O₂P] at e
  exact ⟨fun h => by haveI : FiniteDimensional ℂ (HP₀ W) := h; exact e.finiteDimensional,
    fun h => by haveI := h; exact e.symm.finiteDimensional⟩

/-- Forward direction of `etingofFinite_iff_quot_O₂P`. -/
theorem finiteDimensional_quot_O₂P_of_etingofFinite (W : VertexOperatorAlgebra 𝒱)
    (hE : EtingofFinite W) : FiniteDimensional ℂ (𝒱 ⧸ O₂P W) :=
  (etingofFinite_iff_quot_O₂P W).mp hE

/-- Backward direction of `etingofFinite_iff_quot_O₂P`. -/
theorem etingofFinite_of_finiteDimensional_quot_O₂P (W : VertexOperatorAlgebra 𝒱)
    (h : FiniteDimensional ℂ (𝒱 ⧸ O₂P W)) : EtingofFinite W :=
  (etingofFinite_iff_quot_O₂P W).mpr h

/-! ## §2  `O₂P` is a graded subspace -/

/-- The **homogeneous** bracket generators `a₍₀₎b`, `a ∈ 𝒱ₚ`, `b ∈ 𝒱_q`. -/
def PhomGen (W : VertexOperatorAlgebra 𝒱) : Set 𝒱 :=
  {x | ∃ (p q : ℤ) (a b : 𝒱), a ∈ W.grading p ∧ b ∈ W.grading q ∧ x = W.smul a 0 b}

/-- A homogeneous bracket generator lands one degree *down*: `a₍₀₎b ∈ 𝒱_{p+q−1}`.  (Contrast the
`₍₋₂₎`-generators of `O₂`, which land one degree *up*, `gen_mem_grading`.) -/
theorem brk_mem_grading (W : VertexOperatorAlgebra 𝒱) {p q : ℤ} {a b : 𝒱}
    (ha : a ∈ W.grading p) (hb : b ∈ W.grading q) :
    W.smul a 0 b ∈ W.grading (p + q - 1) := by
  have h := W.smul_mem_grading ha hb 0
  rwa [show p + q - 0 - 1 = p + q - 1 from by ring] at h

/-- For homogeneous `a` and arbitrary `b`, `a₍₀₎b` lies in the span of homogeneous generators. -/
theorem genHomA_mem_span_PhomGen (W : VertexOperatorAlgebra 𝒱) {p : ℤ} {a : 𝒱}
    (ha : a ∈ W.grading p) (b : 𝒱) :
    W.smul a 0 b ∈ Submodule.span ℂ (PhomGen W) := by
  have hb : b ∈ Submodule.span ℂ {x | IsHomog W x} := by rw [span_homog_eq_top]; trivial
  refine Submodule.span_induction
    (p := fun b _ => W.smul a 0 b ∈ Submodule.span ℂ (PhomGen W)) ?_ ?_ ?_ ?_ hb
  · rintro y ⟨q, hq⟩
    exact Submodule.subset_span ⟨p, q, a, y, ha, hq, rfl⟩
  · simp
  · intro y z _ _ hy hz
    rw [W.smul_add_right]; exact (Submodule.span ℂ (PhomGen W)).add_mem hy hz
  · intro c y _ hy
    rw [W.smul_smul_right]; exact (Submodule.span ℂ (PhomGen W)).smul_mem c hy

/-- For arbitrary `a, b`, `a₍₀₎b` lies in the span of homogeneous generators. -/
theorem brk_mem_span_PhomGen (W : VertexOperatorAlgebra 𝒱) (a b : 𝒱) :
    W.smul a 0 b ∈ Submodule.span ℂ (PhomGen W) := by
  have ha : a ∈ Submodule.span ℂ {x | IsHomog W x} := by rw [span_homog_eq_top]; trivial
  refine Submodule.span_induction
    (p := fun a _ => W.smul a 0 b ∈ Submodule.span ℂ (PhomGen W)) ?_ ?_ ?_ ?_ ha
  · rintro y ⟨p, hp⟩; exact genHomA_mem_span_PhomGen W hp b
  · simp
  · intro y z _ _ hy hz
    rw [W.smul_add_left]; exact (Submodule.span ℂ (PhomGen W)).add_mem hy hz
  · intro c y _ hy
    rw [W.smul_smul_left]; exact (Submodule.span ℂ (PhomGen W)).smul_mem c hy

/-- **`poissonUp` is graded**: it is the span of its homogeneous generators. -/
theorem poissonUp_eq_span_PhomGen (W : VertexOperatorAlgebra 𝒱) :
    poissonUp W = Submodule.span ℂ (PhomGen W) := by
  apply le_antisymm
  · rw [poissonUp, Submodule.span_le]
    rintro x ⟨a, b, rfl⟩
    exact brk_mem_span_PhomGen W a b
  · rw [Submodule.span_le]
    rintro x ⟨p, q, a, b, _, _, rfl⟩
    exact Submodule.subset_span ⟨a, b, rfl⟩

/-- The homogeneous generators of `O₂P`: the `₍₋₂₎`-products together with the brackets. -/
def O₂PhomGen (W : VertexOperatorAlgebra 𝒱) : Set 𝒱 := O₂homGen W ∪ PhomGen W

/-- A homogeneous bracket generator is homogeneous. -/
theorem PhomGen_homog (W : VertexOperatorAlgebra 𝒱) {g : 𝒱} (hg : g ∈ PhomGen W) :
    IsHomog W g := by
  obtain ⟨p, q, a, b, ha, hb, rfl⟩ := hg
  exact ⟨p + q - 1, brk_mem_grading W ha hb⟩

/-- Every generator of `O₂P` is homogeneous. -/
theorem O₂PhomGen_homog (W : VertexOperatorAlgebra 𝒱) {g : 𝒱} (hg : g ∈ O₂PhomGen W) :
    IsHomog W g := by
  rcases hg with hg | hg
  · exact O₂homGen_homog W hg
  · exact PhomGen_homog W hg

/-- **`O₂P` is graded**: it is the span of its homogeneous generators. -/
theorem O₂P_eq_span_O₂PhomGen (W : VertexOperatorAlgebra 𝒱) :
    O₂P W = Submodule.span ℂ (O₂PhomGen W) := by
  rw [O₂P, O₂_eq_span_homGen, poissonUp_eq_span_PhomGen, O₂PhomGen, Submodule.span_union]

/-- `π_n` maps `O₂P` into `O₂P`. -/
theorem piHom_maps_O₂P (W : VertexOperatorAlgebra 𝒱) (n : ℤ) {x : 𝒱} (hx : x ∈ O₂P W) :
    piHom W n x ∈ O₂P W := by
  rw [O₂P_eq_span_O₂PhomGen] at hx ⊢
  exact piHom_maps_span_homog W n (O₂PhomGen W) (fun g hg => O₂PhomGen_homog W hg) hx

/-- **Graded spanning, augmented.**  The `O₂P`-analogue of `grading_le_span_sup_O₂_inf`. -/
theorem grading_le_span_sup_O₂P_inf (W : VertexOperatorAlgebra 𝒱) (S : Set 𝒱)
    (hShom : ∀ s ∈ S, IsHomog W s)
    (htop : (⊤ : Submodule ℂ 𝒱) = Submodule.span ℂ S ⊔ O₂P W) (n : ℤ) :
    W.grading n ≤ Submodule.span ℂ S ⊔ (O₂P W ⊓ W.grading n) := by
  intro x hx
  have hxtop : x ∈ Submodule.span ℂ S ⊔ O₂P W := htop ▸ Submodule.mem_top
  rw [Submodule.mem_sup] at hxtop
  obtain ⟨a, ha, b, hb, rfl⟩ := hxtop
  have hpix : piHom W n (a + b) = a + b := piHom_of_mem W hx
  rw [map_add] at hpix
  have hpa_S : piHom W n a ∈ Submodule.span ℂ S := piHom_maps_span_homog W n S hShom ha
  have hpb_O : piHom W n b ∈ O₂P W := piHom_maps_O₂P W n hb
  have hpb_g : piHom W n b ∈ W.grading n := piHom_mem W n b
  rw [← hpix]
  exact Submodule.add_mem_sup hpa_S ⟨hpb_O, hpb_g⟩

/-- The bracket generators of *exact* degree `n`. -/
def PhomGenDeg (W : VertexOperatorAlgebra 𝒱) (n : ℤ) : Set 𝒱 :=
  {x | ∃ (p q : ℤ) (a b : 𝒱), a ∈ W.grading p ∧ b ∈ W.grading q ∧ p + q - 1 = n ∧
    x = W.smul a 0 b}

/-- All degree-`n` generators of `O₂P`. -/
def O₂PhomGenDeg (W : VertexOperatorAlgebra 𝒱) (n : ℤ) : Set 𝒱 :=
  O₂homGenDeg W n ∪ PhomGenDeg W n

/-- `π_n` sends a homogeneous bracket generator into `span (PhomGenDeg W n)`. -/
theorem piHom_PhomGen_mem (W : VertexOperatorAlgebra 𝒱) (n : ℤ) {g : 𝒱}
    (hg : g ∈ PhomGen W) : piHom W n g ∈ Submodule.span ℂ (PhomGenDeg W n) := by
  obtain ⟨p, q, a, b, ha, hb, rfl⟩ := hg
  by_cases hd : p + q - 1 = n
  · rw [piHom_of_mem W (by rw [← hd]; exact brk_mem_grading W ha hb)]
    exact Submodule.subset_span ⟨p, q, a, b, ha, hb, hd, rfl⟩
  · rw [piHom_of_mem_ne W (k := p + q - 1) (by omega) (brk_mem_grading W ha hb)]
    exact (Submodule.span ℂ (PhomGenDeg W n)).zero_mem

/-- `π_n` sends a homogeneous `O₂P`-generator into `span (O₂PhomGenDeg W n)`. -/
theorem piHom_O₂PhomGen_mem (W : VertexOperatorAlgebra 𝒱) (n : ℤ) {g : 𝒱}
    (hg : g ∈ O₂PhomGen W) : piHom W n g ∈ Submodule.span ℂ (O₂PhomGenDeg W n) := by
  rcases hg with hg | hg
  · exact Submodule.span_mono Set.subset_union_left (piHom_homGen_mem W n hg)
  · exact Submodule.span_mono Set.subset_union_right (piHom_PhomGen_mem W n hg)

/-- **Graded reduction of `O₂P ⊓ 𝒱ₙ`**: it lies in the span of the *degree-`n`* generators. -/
theorem O₂P_inf_grading_le_span_deg (W : VertexOperatorAlgebra 𝒱) (n : ℤ) :
    O₂P W ⊓ W.grading n ≤ Submodule.span ℂ (O₂PhomGenDeg W n) := by
  intro x hx
  obtain ⟨hxO, hxg⟩ := hx
  rw [O₂P_eq_span_O₂PhomGen] at hxO
  rw [← piHom_of_mem W hxg]
  refine Submodule.span_induction
    (p := fun y _ => piHom W n y ∈ Submodule.span ℂ (O₂PhomGenDeg W n)) ?_ ?_ ?_ ?_ hxO
  · intro g hg; exact piHom_O₂PhomGen_mem W n hg
  · simp only [map_zero]; exact (Submodule.span ℂ (O₂PhomGenDeg W n)).zero_mem
  · intro y z _ _ hy hz; rw [map_add]
    exact (Submodule.span ℂ (O₂PhomGenDeg W n)).add_mem hy hz
  · intro c y _ hy; rw [map_smul]
    exact (Submodule.span ℂ (O₂PhomGenDeg W n)).smul_mem c hy

/-! ## §3  Mode-`0` triangularity: `a[0]b = a₍₀₎b + (higher modes)`

This is the one genuinely new ingredient of Arakawa–Kawasetsu §5.  In Zhu's argument the
generators `a[0]v` of the relation space were *free* — no use was made of them.  Passing to the
associated graded by conformal weight, their leading term is exactly the Poisson bracket `a₍₀₎v`,
so the relation space already contains representatives of `{R_V, R_V}` and the finite-generation
argument goes through with `dim R_V ⧸ {R_V, R_V} < ∞` in place of `dim R_V < ∞`.

The repository realises "pass to `gr`" not by building an associated-graded object but by the
downward strong induction on conformal degree already used for the `₍₋₂₎`-generators
(`grading_le_pullbackG`); `sqDefect0_mem_of_lower` is the statement that the non-leading terms sit
in strictly lower degree.
-/

/-- The mode-`0` analogue of `sqDefect`: the tail `∑_{i ≠ 0} c_i a₍ᵢ₎b` of `a[0]b`. -/
noncomputable def sqDefect0 (W : VertexOperatorAlgebra 𝒱) (a : 𝒱) (p : ℕ) (b : 𝒱) : 𝒱 :=
  ∑ᶠ i : ℤ, (if i = 0 then (0 : ℂ) else sqBracketCoeffZ p 0 i) • mode (W.Y a) i b

/-- The defining sum of `sqDefect0` has finite support. -/
theorem sqDefect0_support_finite (W : VertexOperatorAlgebra 𝒱) (a : 𝒱) (p : ℕ) (b : 𝒱) :
    (Function.support fun i : ℤ =>
      (if i = 0 then (0 : ℂ) else sqBracketCoeffZ p 0 i) • mode (W.Y a) i b).Finite := by
  refine Set.Finite.subset (sqModeZ_support_finite W a p 0 b) (fun i hi => ?_)
  simp only [Function.mem_support, ne_eq] at hi ⊢
  intro hc
  apply hi
  by_cases h2 : i = 0
  · rw [if_pos h2, zero_smul]
  · rw [if_neg h2, hc]

/-- **Triangularity at `m = 0`**: `a[0]b = a₍₀₎b + (strictly higher modes)`.  The mode-`0`
coefficient of the square bracket is `1` (`sqBracketCoeffZ_diag'`), and every other contributing
mode is `≥ 1`. -/
theorem vSqZ_zero_eq (W : VertexOperatorAlgebra 𝒱) (a : 𝒱) (p : ℕ) (b : 𝒱) :
    vSqZ W a p 0 b = mode (W.Y a) 0 b + sqDefect0 W a p b := by
  rw [vSqZ_apply, sqDefect0]
  have hsplit : ∀ i : ℤ, sqBracketCoeffZ p 0 i • mode (W.Y a) i b
      = (if i = 0 then sqBracketCoeffZ p 0 i • mode (W.Y a) i b else 0)
        + (if i = 0 then (0 : ℂ) else sqBracketCoeffZ p 0 i) • mode (W.Y a) i b := by
    intro i
    by_cases h2 : i = 0
    · rw [if_pos h2, if_pos h2, zero_smul, add_zero]
    · rw [if_neg h2, if_neg h2, zero_add]
  rw [finsum_congr hsplit]
  have hfin1 : (Function.support fun i : ℤ =>
      (if i = 0 then sqBracketCoeffZ p 0 i • mode (W.Y a) i b else 0)).Finite := by
    refine Set.Finite.subset (Set.finite_singleton (0 : ℤ)) (fun i hi => ?_)
    simp only [Function.mem_support, ne_eq] at hi
    by_contra hne
    exact hi (if_neg hne)
  rw [finsum_add_distrib hfin1 (sqDefect0_support_finite W a p b)]
  congr 1
  rw [finsum_eq_single _ (0 : ℤ) (fun i hi => if_neg hi), if_pos rfl,
    sqBracketCoeffZ_diag' p 0, one_smul]

/-- **The mode-`0` defect lies strictly below degree `p + q − 1`.**  This is the "leading term"
statement: modulo everything of lower conformal weight, `a[0]b` *is* the Poisson bracket `a₍₀₎b`. -/
theorem sqDefect0_mem_of_lower (W : VertexOperatorAlgebra 𝒱) {p q n : ℤ} {a b : 𝒱}
    (ha : a ∈ W.grading p) (hb : b ∈ W.grading q)
    (hpq : p + q - 1 = n) (T : Submodule ℂ 𝒱)
    (hT : ∀ m : ℤ, m < n → W.grading m ≤ T) :
    sqDefect0 W a p.toNat b ∈ T := by
  rw [sqDefect0]
  refine finsum_mem_submodule_pd _ _ (fun i => ?_)
  by_cases h2 : i = 0
  · rw [if_pos h2, zero_smul]; exact Submodule.zero_mem _
  rw [if_neg h2]
  rcases lt_or_ge i (0 : ℤ) with hlt | hge
  · rw [sqBracketCoeffZ_of_lt _ hlt, zero_smul]; exact Submodule.zero_mem _
  · have hi : (1 : ℤ) ≤ i := by omega
    refine Submodule.smul_mem _ _ ?_
    have hmem : W.smul a i b ∈ W.grading (p + q - i - 1) := W.smul_mem_grading ha hb i
    exact hT _ (by omega) hmem

/-! ## §4  Arakawa–Kawasetsu Proposition 5.2 -/

section

variable (W : VertexOperatorAlgebra 𝒱)

/-- **The `a[0]`-generators are already in the relation module.**  This is Zhu's relation (5.1),
which is one of the two defining families of `blockRelSpanG`; Arakawa–Kawasetsu's observation is
that it was never used in Zhu's proof and is exactly what is needed to weaken the hypothesis. -/
theorem vSqZ_zero_mem_blockRelSpanG {ka : ℕ} (hka : 1 ≤ ka) {a : 𝒱}
    (ha : a ∈ W.grading (ka : ℤ)) (v : 𝒱) :
    (ιG (vSqZ W a ka 0 v) : 𝒱G 𝒱) ∈ blockRelSpanG W :=
  Submodule.subset_span (Or.inl ⟨ka, a, v, hka, ha, rfl⟩)

/-- The `₍₋₂₎`-generator step of the degree induction, extracted from `grading_le_pullbackG`
(where it appears inline). -/
theorem negTwo_mem_pullbackG (hzero : VacuumGradeZero W) {p q n : ℤ} {a b : 𝒱}
    (ha : a ∈ W.grading p) (hb : b ∈ W.grading q) (hpq : p + q + 1 = n)
    (T : Submodule (↥GSeries) (𝒱G 𝒱)) (hT : ∀ m : ℤ, m < n → W.grading m ≤ pullbackG T)
    (hrel : blockRelSpanG W ≤ T) :
    W.smul a (-2) b ∈ pullbackG T := by
  classical
  rcases lt_or_ge p 0 with hp | hp0
  · have ha0 : a = 0 := by
      rw [W.positivity p hp, Submodule.mem_bot] at ha; exact ha
    rw [ha0, W.smul_zero_left]
    exact Submodule.zero_mem _
  have hexp := vSqZ_neg_two_eq W a p.toNat b
  have hstep : W.smul a (-2) b = vSqZ W a p.toNat (-2) b - sqDefect W a p.toNat b := by
    rw [hexp]
    show W.smul a (-2) b = mode (W.Y a) (-2) b + sqDefect W a p.toNat b
      - sqDefect W a p.toNat b
    rw [add_sub_cancel_right]
    rfl
  rw [hstep]
  refine Submodule.sub_mem _ ?_ (sqDefect_mem_of_lower W ha hb hpq hp0 (pullbackG T) hT)
  rcases eq_or_lt_of_le hp0 with hp | hp1
  · have ha0 : a ∈ W.grading 0 := by rw [hp]; exact ha
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp (hzero ha0)
    have hp0' : p.toNat = 0 := by omega
    rw [hp0']
    have hlin : vSqZ W (c • W.vacuum) 0 (-2) b = c • vSqZ W W.vacuum 0 (-2) b := by
      rw [vSqZ_apply, vSqZ_apply,
        smul_finsum' c (sqModeZ_support_finite W W.vacuum 0 (-2) b)]
      refine finsum_congr (fun i => ?_)
      change sqBracketCoeffZ 0 (-2) i • W.smul (c • W.vacuum) i b
        = c • (sqBracketCoeffZ 0 (-2) i • W.smul W.vacuum i b)
      rw [PreVertexAlgebra.smul_smul_left, smul_comm]
    rw [hlin, vSqZ_vacuum_scalar, smul_smul]
    refine Submodule.smul_mem _ _ (hT q (by omega) hb)
  · exact vSqZ_negTwo_mem_of_blockRelSpanG W ha hb hp1 hpq T hT hrel

/-- **The bracket generator descends** — the new step.  For homogeneous `a ∈ 𝒱ₚ`, `b ∈ 𝒱_q`
with `p + q − 1 = n`, the Poisson representative `a₍₀₎b` lies in `pullbackG T` as soon as every
strictly lower degree does.

Compare `negTwo_mem_pullbackG`: this step is *easier*, because the `a[0]`-relation is exact — there
is no Eisenstein tail to absorb, hence no `vSqZ_mem_of_lower` bookkeeping and no `GSeries` scalar.
That is precisely Arakawa–Kawasetsu's "the generators `a[0]b` were free in Zhu's argument". -/
theorem brk_mem_pullbackG (hzero : VacuumGradeZero W) {p q n : ℤ} {a b : 𝒱}
    (ha : a ∈ W.grading p) (hb : b ∈ W.grading q) (hpq : p + q - 1 = n)
    (T : Submodule (↥GSeries) (𝒱G 𝒱)) (hT : ∀ m : ℤ, m < n → W.grading m ≤ pullbackG T)
    (hrel : blockRelSpanG W ≤ T) :
    W.smul a 0 b ∈ pullbackG T := by
  rcases lt_or_ge p 0 with hp | hp0
  · have ha0 : a = 0 := by
      rw [W.positivity p hp, Submodule.mem_bot] at ha; exact ha
    rw [ha0, W.smul_zero_left]
    exact Submodule.zero_mem _
  rcases eq_or_lt_of_le hp0 with hp | hp1
  · -- `p = 0`: `a = c·𝟙` and `𝟙₍₀₎b = 0`.
    have ha0 : a ∈ W.grading 0 := by rw [hp]; exact ha
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp (hzero ha0)
    rw [PreVertexAlgebra.smul_smul_left, W.smul_vacuum_left, if_neg (by norm_num), smul_zero]
    exact Submodule.zero_mem _
  · -- `p ≥ 1`: the exact `a[0]`-relation, minus a strictly lower-degree defect.
    have hka : 1 ≤ p.toNat := by omega
    have ha' : a ∈ W.grading ((p.toNat : ℕ) : ℤ) := by
      rwa [show ((p.toNat : ℕ) : ℤ) = p from by omega]
    have hrelmem : vSqZ W a p.toNat 0 b ∈ pullbackG T :=
      hrel (vSqZ_zero_mem_blockRelSpanG W hka ha' b)
    have hdef : sqDefect0 W a p.toNat b ∈ pullbackG T :=
      sqDefect0_mem_of_lower W ha hb hpq (pullbackG T) hT
    have hstep : W.smul a 0 b = vSqZ W a p.toNat 0 b - sqDefect0 W a p.toNat b := by
      rw [vSqZ_zero_eq W a p.toNat b]
      show W.smul a 0 b = mode (W.Y a) 0 b + sqDefect0 W a p.toNat b - sqDefect0 W a p.toNat b
      rw [add_sub_cancel_right]
      rfl
    rw [hstep]
    exact Submodule.sub_mem _ hrelmem hdef

/-- **The degree induction, with the augmented relation space.**  Verbatim
`grading_le_pullbackG` except that the spanning hypothesis is modulo `O₂P W = O₂ W + {𝒱,𝒱}` rather
than modulo `O₂ W`, and the induction therefore has a second generator branch, `brk_mem_pullbackG`.
-/
theorem grading_le_pullbackG_of_poisson (hzero : VacuumGradeZero W) (S : Set 𝒱)
    (hShom : ∀ s ∈ S, IsHomog W s)
    (htop : (⊤ : Submodule ℂ 𝒱) = Submodule.span ℂ S ⊔ O₂P W)
    (T : Submodule (↥GSeries) (𝒱G 𝒱))
    (hS : ∀ s ∈ S, (ιG s : 𝒱G 𝒱) ∈ T)
    (hrel : blockRelSpanG W ≤ T) (n : ℤ) :
    W.grading n ≤ pullbackG T := by
  classical
  have hSle : Submodule.span ℂ S ≤ pullbackG T := by
    rw [Submodule.span_le]
    intro s hs
    exact hS s hs
  rcases lt_or_ge n 0 with hneg | hnn
  · rw [W.positivity n hneg]; exact bot_le
  obtain ⟨N, rfl⟩ : ∃ N : ℕ, n = (N : ℤ) := ⟨n.toNat, by omega⟩
  induction N using Nat.strong_induction_on with
  | _ N ihN =>
    have hT : ∀ m : ℤ, m < (N : ℤ) → W.grading m ≤ pullbackG T := by
      intro m hm
      rcases lt_or_ge m 0 with hm0 | hm0
      · rw [W.positivity m hm0]; exact bot_le
      · obtain ⟨M, rfl⟩ : ∃ M : ℕ, m = (M : ℤ) := ⟨m.toNat, by omega⟩
        exact ihN M (by exact_mod_cast hm) (by exact_mod_cast hm0)
    refine le_trans (grading_le_span_sup_O₂P_inf W S hShom htop (N : ℤ)) ?_
    refine sup_le hSle ?_
    refine le_trans (O₂P_inf_grading_le_span_deg W (N : ℤ)) ?_
    rw [Submodule.span_le]
    rintro g (⟨p, q, a, b, ha, hb, hpq, rfl⟩ | ⟨p, q, a, b, ha, hb, hpq, rfl⟩)
    · exact negTwo_mem_pullbackG W hzero ha hb hpq T hT hrel
    · exact brk_mem_pullbackG W hzero ha hb hpq T hT hrel

/-- The pullback form. -/
theorem pullbackG_eq_top_of_poisson (hzero : VacuumGradeZero W) (S : Set 𝒱)
    (hShom : ∀ s ∈ S, IsHomog W s)
    (htop : (⊤ : Submodule ℂ 𝒱) = Submodule.span ℂ S ⊔ O₂P W)
    (T : Submodule (↥GSeries) (𝒱G 𝒱))
    (hS : ∀ s ∈ S, (ιG s : 𝒱G 𝒱) ∈ T) (hrel : blockRelSpanG W ≤ T) :
    pullbackG T = ⊤ := by
  refine le_antisymm le_top ?_
  rw [← span_homog_eq_top W, Submodule.span_le]
  rintro x ⟨m, hx⟩
  exact grading_le_pullbackG_of_poisson W hzero S hShom htop T hS hrel m hx

/-- **Arakawa–Kawasetsu Proposition 5.2, span form.**  A finite family spanning `𝒱` modulo
`O₂(𝒱) + {𝒱,𝒱}` already generates `𝒱G = ℂ[G₂,G₄,G₆] ⊗ 𝒱` over `ℂ[G₂,G₄,G₆]` modulo the relation
module `blockRelSpanG` (= AK's `[V_A, V_A] + O_q(V)`).

This is the identical conclusion of `span_sup_blockRelSpanG_eq_top` (Zhu Lemma 4.4.1 / DLM Lemma
5.2) under a **strictly weaker** spanning hypothesis, which is exactly the content of AK §5. -/
theorem span_sup_blockRelSpanG_eq_top_of_poisson (hzero : VacuumGradeZero W) (S : Set 𝒱)
    (hShom : ∀ s ∈ S, IsHomog W s)
    (htop : (⊤ : Submodule ℂ 𝒱) = Submodule.span ℂ S ⊔ O₂P W) :
    (⊤ : Submodule (↥GSeries) (𝒱G 𝒱))
      = Submodule.span (↥GSeries) ((ιG : 𝒱 →ₗ[ℂ] 𝒱G 𝒱) '' S) ⊔ blockRelSpanG W := by
  set T : Submodule (↥GSeries) (𝒱G 𝒱) :=
    Submodule.span (↥GSeries) ((ιG : 𝒱 →ₗ[ℂ] 𝒱G 𝒱) '' S) ⊔ blockRelSpanG W with hTdef
  have hS : ∀ s ∈ S, (ιG s : 𝒱G 𝒱) ∈ T := fun s hs =>
    Submodule.mem_sup_left (Submodule.subset_span ⟨s, hs, rfl⟩)
  have hrel : blockRelSpanG W ≤ T := le_sup_right
  have hpb := pullbackG_eq_top_of_poisson W hzero S hShom htop T hS hrel
  refine le_antisymm ?_ le_top
  rw [← span_range_ιG_eq_top (𝒱 := 𝒱), Submodule.span_le]
  rintro _ ⟨v, rfl⟩
  have : v ∈ pullbackG T := by rw [hpb]; trivial
  exact this

end

/-! ## §5  From the Etingof–Schedler hypothesis to the spanning datum

`Modularity.C2Extraction.exists_homog_gen_of_C2Cofinite` turns `dim A₂(𝒱) < ∞` into a finite
homogeneous positive-weight family spanning `𝒱` modulo `O₂ W`.  Its proof never uses anything
about `O₂ W` beyond its being a subspace, so it is reproduced here for a general subspace of
finite codimension and then applied to `O₂P W`.  (The original is stated only for `O₂`, and its
helper `exists_finset_span_sup_O₂` is `private`, so it cannot be reused directly.)
-/

section

variable (W : VertexOperatorAlgebra 𝒱)

/-- **Lifting a finite spanning set through a subspace of finite codimension.**  Generic form of
`exists_finset_span_sup_O₂`. -/
theorem exists_finset_span_sup_of_quot_finite (P : Submodule ℂ 𝒱)
    (hfin : FiniteDimensional ℂ (𝒱 ⧸ P)) :
    ∃ T : Finset 𝒱, (⊤ : Submodule ℂ 𝒱) = Submodule.span ℂ (T : Set 𝒱) ⊔ P := by
  classical
  have hfin' : Module.Finite ℂ (𝒱 ⧸ P) := hfin
  obtain ⟨S, hS⟩ := Module.finite_def.mp hfin'
  have hsurj : Function.Surjective P.mkQ := Submodule.mkQ_surjective P
  have hlift : ∀ a : 𝒱 ⧸ P, P.mkQ (Function.surjInv hsurj a) = a :=
    fun a => Function.surjInv_eq hsurj a
  refine ⟨S.image (Function.surjInv hsurj), le_antisymm ?_ le_top⟩
  intro x _
  have hle : Submodule.span ℂ (S : Set (𝒱 ⧸ P)) ≤
      Submodule.map P.mkQ
        (Submodule.span ℂ ((S.image (Function.surjInv hsurj) : Finset 𝒱) : Set 𝒱)) := by
    rw [Submodule.span_le]
    intro a ha
    exact ⟨Function.surjInv hsurj a, Submodule.subset_span
      (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ (Finset.mem_coe.mp ha))), hlift a⟩
  have hxs : P.mkQ x ∈ Submodule.span ℂ (S : Set (𝒱 ⧸ P)) := by rw [hS]; trivial
  obtain ⟨y, hyN, hyx⟩ := hle hxs
  have hker : x - y ∈ LinearMap.ker P.mkQ := by
    simp only [LinearMap.mem_ker, map_sub, hyx, sub_self]
  rw [Submodule.ker_mkQ] at hker
  have hxeq : x = y + (x - y) := by abel
  rw [hxeq]
  exact Submodule.add_mem _ (Submodule.mem_sup_left hyN) (Submodule.mem_sup_right hker)

/-- **A finite codimension subspace admits a finite homogeneous positive-weight generating family.**
Generic form of `exists_homog_gen_of_C2Cofinite`; the proof is the same (homogenise the lifts,
discard negative degrees by `W.positivity`, absorb degree `0` into `ℂ𝟙` by `W.vacuum_grade`). -/
theorem exists_homog_gen_of_quot_finite (P : Submodule ℂ 𝒱)
    (hfin : FiniteDimensional ℂ (𝒱 ⧸ P)) :
    ∃ (g : ℕ) (gen : Fin g → 𝒱) (wt : Fin g → ℕ),
      (∀ i, 1 ≤ wt i) ∧ (∀ i, gen i ∈ W.grading (wt i : ℤ)) ∧
      (⊤ : Submodule ℂ 𝒱) = Submodule.span ℂ (Set.range gen ∪ {W.vacuum}) ⊔ P := by
  classical
  obtain ⟨T, hT⟩ := exists_finset_span_sup_of_quot_finite P hfin
  have hall : ∀ y : 𝒱, ∃ F : Finset 𝒱,
      (↑F : Set 𝒱) ⊆ {x : 𝒱 | IsHomog W x} ∧ y ∈ Submodule.span ℂ (F : Set 𝒱) := by
    intro y
    have hy : y ∈ Submodule.span ℂ {x : 𝒱 | IsHomog W x} := by
      rw [span_homog_eq_top]; trivial
    exact Submodule.mem_span_finite_of_mem_span hy
  choose F hFsub hFmem using hall
  set U : Finset 𝒱 := T.biUnion F with hU
  have hUhom : ∀ x ∈ U, IsHomog W x := by
    intro x hx
    rw [hU, Finset.mem_biUnion] at hx
    obtain ⟨y, _, hxy⟩ := hx
    exact hFsub y (Finset.mem_coe.mpr hxy)
  have hTU : (T : Set 𝒱) ⊆ (Submodule.span ℂ (U : Set 𝒱) : Set 𝒱) := by
    intro y hy
    refine Submodule.span_mono ?_ (hFmem y)
    intro z hz
    exact Finset.mem_coe.mpr
      (Finset.mem_biUnion.mpr ⟨y, Finset.mem_coe.mp hy, Finset.mem_coe.mp hz⟩)
  have hUtop : (⊤ : Submodule ℂ 𝒱) = Submodule.span ℂ (U : Set 𝒱) ⊔ P := by
    refine le_antisymm ?_ le_top
    rw [hT]
    exact sup_le_sup_right (Submodule.span_le.mpr hTU) _
  have hdegex : ∀ x : 𝒱, ∃ n : ℤ, IsHomog W x → x ∈ W.grading n := by
    intro x
    by_cases h : IsHomog W x
    · obtain ⟨n, hn⟩ := h
      exact ⟨n, fun _ => hn⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  choose deg hdeg using hdegex
  set Pr : Finset (𝒱 × ℕ) :=
    (U.filter (fun x => 1 ≤ deg x)).image (fun x => (x, (deg x).toNat)) with hPr
  have hPprop : ∀ p ∈ Pr, 1 ≤ p.2 ∧ p.1 ∈ W.grading (p.2 : ℤ) := by
    intro p hp
    rw [hPr, Finset.mem_image] at hp
    obtain ⟨x, hx, rfl⟩ := hp
    rw [Finset.mem_filter] at hx
    obtain ⟨hxU, hx1⟩ := hx
    have hxg : x ∈ W.grading (deg x) := hdeg x (hUhom x hxU)
    refine ⟨by simpa using (by omega : 1 ≤ (deg x).toNat), ?_⟩
    have hcast : (((deg x).toNat : ℕ) : ℤ) = deg x := Int.toNat_of_nonneg (by omega)
    simpa [hcast] using hxg
  have hvac : W.grading 0 = Submodule.span ℂ ({W.vacuum} : Set 𝒱) := W.vacuum_grade
  have hUle : Submodule.span ℂ (U : Set 𝒱) ≤
      Submodule.span ℂ ((fun p : 𝒱 × ℕ => p.1) '' (Pr : Set (𝒱 × ℕ)) ∪ {W.vacuum}) := by
    rw [Submodule.span_le]
    intro x hxU
    have hxU' : x ∈ U := Finset.mem_coe.mp hxU
    have hxg : x ∈ W.grading (deg x) := hdeg x (hUhom x hxU')
    rcases lt_trichotomy (deg x) 0 with h | h | h
    · have hx0 : x = 0 := by
        rw [W.positivity _ h, Submodule.mem_bot] at hxg; exact hxg
      rw [hx0]; exact Submodule.zero_mem _
    · rw [h, hvac] at hxg
      refine Submodule.span_mono (fun z hz => Or.inr hz) hxg
    · have h1 : (1 : ℤ) ≤ deg x := by omega
      refine Submodule.subset_span (Or.inl ⟨(x, (deg x).toNat), ?_, rfl⟩)
      exact Finset.mem_coe.mpr
        (by rw [hPr]; exact Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hxU', h1⟩))
  have e : {x // x ∈ Pr} ≃ Fin Pr.card := Pr.equivFin
  refine ⟨Pr.card, fun i => ((e.symm i : 𝒱 × ℕ)).1, fun i => ((e.symm i : 𝒱 × ℕ)).2,
    fun i => (hPprop _ (e.symm i).2).1, fun i => (hPprop _ (e.symm i).2).2, ?_⟩
  have hrange : Set.range (fun i : Fin Pr.card => ((e.symm i : 𝒱 × ℕ)).1)
      = (fun p : 𝒱 × ℕ => p.1) '' (Pr : Set (𝒱 × ℕ)) := by
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨(e.symm i : 𝒱 × ℕ), Finset.mem_coe.mpr (e.symm i).2, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨e ⟨p, Finset.mem_coe.mp hp⟩, by simp⟩
  refine le_antisymm ?_ le_top
  rw [hUtop]
  refine sup_le_sup_right ?_ _
  rw [hrange]
  exact hUle

/-- **The Arakawa–Kawasetsu spanning datum, from the Etingof–Schedler hypothesis.**
`EtingofFinite W` yields a finite family of homogeneous vectors of strictly positive conformal
weight spanning `𝒱` modulo `O₂(𝒱) + {𝒱,𝒱}`. -/
theorem exists_homog_gen_of_etingofFinite (hE : EtingofFinite W) :
    ∃ (g : ℕ) (gen : Fin g → 𝒱) (wt : Fin g → ℕ),
      (∀ i, 1 ≤ wt i) ∧ (∀ i, gen i ∈ W.grading (wt i : ℤ)) ∧
      (⊤ : Submodule ℂ 𝒱) = Submodule.span ℂ (Set.range gen ∪ {W.vacuum}) ⊔ O₂P W :=
  exists_homog_gen_of_quot_finite W (O₂P W) (finiteDimensional_quot_O₂P_of_etingofFinite W hE)

end

/-! ## §6  Arakawa–Kawasetsu Proposition 5.2, and the growth datum

`Modularity.BlockGrowth.onePointSubexp_of_c2` discharges the ODE-residual of Zhu's theorem from
`C2Cofinite W`.  Every use of `C2Cofinite` in that chain funnels through **one** place —
`Modularity.FormalBlockFinite.fg_blockSpan`, via `exists_homog_gen_of_C2Cofinite` — so replacing
that one input by the Arakawa–Kawasetsu datum of §5 replays the whole chain verbatim under the
weaker hypothesis.  The proofs below are ports of `fg_blockSpan`, `fg_blockSpanS`,
`exists_system_matrix` and `subexponential_block_of_c2` with the hypothesis moved; nothing in them
is new mathematics, and the two genuinely analytic inputs (`qD_mem_blockSpanS`,
`subexponential_of_system`) are used unchanged because they never mentioned `C₂` at all.
-/

section

variable (W : VertexOperatorAlgebra 𝒱)

/-- **Arakawa–Kawasetsu Proposition 5.2.**  For a vertex operator algebra satisfying the
Etingof–Schedler hypothesis, `V_A ⧸ ([V_A, V_A] + O_q(V))` is a finitely generated `A`-module,
where `A = ℂ[G₂,G₄,G₆]` (`GSeries`), `V_A = A ⊗_ℂ 𝒱` (`𝒱G`) and `[V_A,V_A] + O_q(V)` is
`blockRelSpanG W`.

This is the identical conclusion of `moduleFinite_quot_blockRelSpanG` (Zhu Lemma 4.4.1 / DLM Lemma
5.2) with `C2Cofinite W` weakened to `EtingofFinite W`.

⚠ **Why the quotient module is not named here.**  The literal statement
`Module.Finite (↥GSeries) ((𝒱G 𝒱) ⧸ blockRelSpanG W)` — which is what
`moduleFinite_quot_blockRelSpanG` says — **cannot be re-elaborated outside**
`Modularity.BlockRelSpanG`.  Outside that file, `AddCommMonoid (𝒱G 𝒱)` is synthesised as
`TensorProduct.addCommMonoid` and `Semiring ↥GSeries` as `Subalgebra.toSemiring`, whereas
`Submodule.hasQuotient` demands the shapes `AddCommGroup.toAddCommMonoid` and `Ring.toSemiring`;
the two `Submodule` types are then not reducibly defeq and `HasQuotient` fails to synthesise.  (The
existing theorem is fine and can still be *applied*; only its statement cannot be *restated*.)  The
formulation below is the same assertion with the quotient replaced by the finite generating family
it asserts the existence of, which is also the form every consumer in this repository uses. -/
theorem exists_finite_gen_sup_blockRelSpanG_of_etingofFinite (hzero : VacuumGradeZero W)
    (hE : EtingofFinite W) :
    ∃ T : Set (𝒱G 𝒱), T.Finite ∧
      (⊤ : Submodule (↥GSeries) (𝒱G 𝒱))
        = Submodule.span (↥GSeries) T ⊔ blockRelSpanG W := by
  classical
  obtain ⟨g, gen, wt, hwt, hgen, hdec⟩ := exists_homog_gen_of_etingofFinite W hE
  set S : Set 𝒱 := Set.range gen ∪ {W.vacuum} with hSdef
  have hShom : ∀ s ∈ S, IsHomog W s := by
    rintro s (⟨i, rfl⟩ | hs)
    · exact ⟨(wt i : ℤ), hgen i⟩
    · rw [Set.mem_singleton_iff] at hs
      exact ⟨0, hs ▸ W.vacuum_mem_grading_zero⟩
  have hSfin : S.Finite := (Set.finite_range gen).union (Set.finite_singleton _)
  exact ⟨(ιG : 𝒱 →ₗ[ℂ] 𝒱G 𝒱) '' S, hSfin.image _,
    span_sup_blockRelSpanG_eq_top_of_poisson W hzero S hShom hdec⟩

/-- **The block span is finitely generated over `ℂ[G₂,G₄,G₆]`**, from `EtingofFinite`.
Port of `Modularity.FormalBlockFinite.fg_blockSpan`. -/
theorem fg_blockSpan_of_etingofFinite {S : 𝒱 →ₗ[ℂ] FormalQSeries} {hbase : ℂ}
    (hsupp : ∀ v, S v ∈ QSeriesAt hbase) (hS : IsFormalBlock W S)
    (hzero : VacuumGradeZero W) (hE : EtingofFinite W) :
    (Submodule.span (↥GSeries)
      (Set.range (blockRestrict hsupp : 𝒱 →ₗ[ℂ] ↥(QSeriesAt hbase)))).FG := by
  classical
  obtain ⟨g, gen, wt, hwt, hgen, hdec⟩ := exists_homog_gen_of_etingofFinite W hE
  set Sset : Set 𝒱 := Set.range gen ∪ {W.vacuum} with hSdef
  have hShom : ∀ s ∈ Sset, IsHomog W s := by
    rintro s (⟨i, rfl⟩ | hs)
    · exact ⟨(wt i : ℤ), hgen i⟩
    · rw [Set.mem_singleton_iff] at hs
      exact ⟨0, hs ▸ W.vacuum_mem_grading_zero⟩
  have htop := span_sup_blockRelSpanG_eq_top_of_poisson W hzero Sset hShom hdec
  have hSfin : Sset.Finite := (Set.finite_range gen).union (Set.finite_singleton _)
  have hker := blockRelSpanG_le_ker W hsupp hS
  have hmapbot : Submodule.map (blockLift hsupp) (blockRelSpanG W) = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨x, hx, rfl⟩
    exact LinearMap.mem_ker.mp (hker hx)
  have himg : (blockLift hsupp) '' ((ιG : 𝒱 →ₗ[ℂ] 𝒱G 𝒱) '' Sset)
      = (blockRestrict hsupp) '' Sset := by
    rw [Set.image_image]
    exact Set.image_congr (fun v _ => blockLift_ιG hsupp v)
  have h1 : Submodule.span (↥GSeries)
      (Set.range (blockRestrict hsupp : 𝒱 →ₗ[ℂ] ↥(QSeriesAt hbase)))
      = LinearMap.range (blockLift hsupp) := by
    rw [blockLift, LinearMap.range_liftBaseChange, LinearMap.coe_range]
  have h2 : LinearMap.range (blockLift hsupp)
      = Submodule.span (↥GSeries) ((blockRestrict hsupp) '' Sset) := by
    rw [LinearMap.range_eq_map, htop, Submodule.map_sup, hmapbot, sup_bot_eq,
      Submodule.map_span, himg]
  rw [h1, h2]
  exact Submodule.fg_span (hSfin.image _)

/-- The `SubexpPS`-span is finitely generated, from finite generation over `GSeries`.  Port of
`Modularity.BlockSystem.fg_blockSpanS`, with the `GSeries` finiteness taken as a hypothesis. -/
theorem fg_blockSpanS_of_fg {S : 𝒱 →ₗ[ℂ] FormalQSeries} {hbase : ℂ}
    (hsupp : ∀ v, S v ∈ QSeriesAt hbase)
    (hfg : (Submodule.span (↥GSeries)
      (Set.range (blockRestrict hsupp : 𝒱 →ₗ[ℂ] ↥(QSeriesAt hbase)))).FG) :
    (blockSpanS hsupp).FG := by
  classical
  obtain ⟨T, hT⟩ := hfg
  refine ⟨T, ?_⟩
  refine le_antisymm ?_ ?_
  · rw [Submodule.span_le]
    intro z hz
    have hz' : z ∈ Submodule.span (↥GSeries)
        (Set.range (blockRestrict hsupp : 𝒱 →ₗ[ℂ] ↥(QSeriesAt hbase))) := by
      rw [← hT]; exact Submodule.subset_span hz
    exact span_GSeries_le_span_SubexpPS _ z hz'
  · rw [blockSpanS, Submodule.span_le]
    rintro _ ⟨v, rfl⟩
    refine span_GSeries_le_span_SubexpPS (X := (T : Set ↥(QSeriesAt hbase))) _ ?_
    rw [hT]
    exact Submodule.subset_span ⟨v, rfl⟩

/-- The first-order system, from finite generation of the block span.  Port of
`Modularity.BlockSystem.exists_system_matrix` with `C2Cofinite` replaced by the finiteness it was
only ever used to produce. -/
theorem exists_system_matrix_of_fg {S : 𝒱 →ₗ[ℂ] FormalQSeries} {hbase : ℂ}
    (hsupp : ∀ v, S v ∈ QSeriesAt hbase) (hS : IsFormalBlock W S)
    (hfgS : (blockSpanS hsupp).FG) :
    ∃ (g : ℕ) (y : Fin g → ↥(QSeriesAt hbase)) (A : Fin g → Fin g → ↥SubexpPS),
      (∀ k, qD hbase (y k) = ∑ l, A k l • y l) ∧
      (∀ v : 𝒱, ∃ c : Fin g → ↥SubexpPS,
        blockRestrict hsupp v = ∑ l, c l • y l) := by
  classical
  obtain ⟨g, y, hy⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hfgS
  have hmemy : ∀ k : Fin g, y k ∈ blockSpanS hsupp := by
    intro k
    rw [← hy]
    exact Submodule.subset_span ⟨k, rfl⟩
  have hA : ∀ k : Fin g, ∃ c : Fin g → ↥SubexpPS, ∑ l, c l • y l = qD hbase (y k) := by
    intro k
    refine (Submodule.mem_span_range_iff_exists_fun (↥SubexpPS)).mp ?_
    rw [hy]
    exact qD_mem_blockSpanS W hsupp hS (hmemy k)
  choose A hAeq using hA
  refine ⟨g, y, A, fun k => (hAeq k).symm, fun v => ?_⟩
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (↥SubexpPS)).mp
    (by rw [hy]; exact blockRestrict_mem_blockSpanS hsupp v)
  exact ⟨c, hc.symm⟩

set_option maxHeartbeats 1000000 in
-- the same raised limit as the original `subexponential_block_of_c2` this ports; the
-- `psSMul`/`qConv` coefficient identities are heavy to unfold.
/-- Every value of a formal block with finitely generated span is subexponential.  Port of
`Modularity.BlockGrowth.subexponential_block_of_c2`. -/
theorem subexponential_block_of_fg {S : 𝒱 →ₗ[ℂ] FormalQSeries} {hbase : ℂ}
    (hsupp : ∀ v, S v ∈ QSeriesAt hbase) (hS : IsFormalBlock W S)
    (hfgS : (blockSpanS hsupp).FG) (v : 𝒱) :
    Subexponential (fun n : ℕ => ‖S v (hbase + (n : ℂ))‖) := by
  classical
  obtain ⟨g, y, A, hsys, hgen⟩ := exists_system_matrix_of_fg W hsupp hS hfgS
  set z : Fin g → ℕ → ℂ := fun k n => ((y k : ↥(QSeriesAt hbase)) : FormalQSeries)
    (hbase + (n : ℂ)) with hz
  set a : Fin g → Fin g → ℕ → ℂ := fun k l j =>
    PowerSeries.coeff j ((A k l : ↥SubexpPS) : PowerSeries ℂ) with ha
  have haSub : ∀ k l, Subexponential (fun j => ‖a k l j‖) := fun k l => (A k l).2
  have hrec : ∀ (k : Fin g) (Nn : ℕ),
      (hbase + (Nn : ℂ)) * z k Nn
        = ∑ l, ∑ j ∈ Finset.range (Nn + 1), a k l j * z l (Nn - j) := by
    intro k Nn
    have hco : ((qD hbase (y k) : ↥(QSeriesAt hbase)) : FormalQSeries)
        = ((∑ l, A k l • y l : ↥(QSeriesAt hbase)) : FormalQSeries) := by rw [hsys k]
    have hL : ((qD hbase (y k) : ↥(QSeriesAt hbase)) : FormalQSeries) (hbase + (Nn : ℂ))
        = (hbase + (Nn : ℂ)) * z k Nn := rfl
    have hR : ((∑ l, A k l • y l : ↥(QSeriesAt hbase)) : FormalQSeries) (hbase + (Nn : ℂ))
        = ∑ l, ∑ j ∈ Finset.range (Nn + 1), a k l j * z l (Nn - j) := by
      rw [Submodule.coe_sum, Finset.sum_apply]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      change psSMul ((A k l : ↥SubexpPS) : PowerSeries ℂ)
        ((y l : ↥(QSeriesAt hbase)) : FormalQSeries) (hbase + (Nn : ℂ)) = _
      rw [psSMul_apply_coset _ (y l).2 Nn]
    rw [← hL, hco, hR]
  have hzSub : ∀ k, Subexponential (fun n => ‖z k n‖) :=
    subexponential_of_system z a haSub hrec
  obtain ⟨c, hc⟩ := hgen v
  have hcoeff : ∀ n : ℕ, S v (hbase + (n : ℂ))
      = ∑ l, qConv (fun j => PowerSeries.coeff j ((c l : ↥SubexpPS) : PowerSeries ℂ))
          ((y l : ↥(QSeriesAt hbase)) : FormalQSeries) (hbase + (n : ℂ)) := by
    intro n
    have hcv : ((blockRestrict hsupp v : ↥(QSeriesAt hbase)) : FormalQSeries)
        = ((∑ l, c l • y l : ↥(QSeriesAt hbase)) : FormalQSeries) := by rw [hc]
    have hlhs : ((blockRestrict hsupp v : ↥(QSeriesAt hbase)) : FormalQSeries)
        (hbase + (n : ℂ)) = S v (hbase + (n : ℂ)) := rfl
    rw [← hlhs, hcv, Submodule.coe_sum, Finset.sum_apply]
    exact Finset.sum_congr rfl (fun l _ => rfl)
  have hterm : ∀ l : Fin g, Subexponential (fun n : ℕ =>
      ‖qConv (fun j => PowerSeries.coeff j ((c l : ↥SubexpPS) : PowerSeries ℂ))
        ((y l : ↥(QSeriesAt hbase)) : FormalQSeries) (hbase + (n : ℂ))‖) :=
    fun l => subexponential_qConv (c l).2 (QSeriesAt.support_neg (y l).2) (hzSub l)
  refine Subexponential.of_le (fun n => ?_)
    (Subexponential.finsetSum Finset.univ (fun l n =>
      ‖qConv (fun j => PowerSeries.coeff j ((c l : ↥SubexpPS) : PowerSeries ℂ))
        ((y l : ↥(QSeriesAt hbase)) : FormalQSeries) (hbase + (n : ℂ))‖)
      (fun l _ => hterm l))
  rw [hcoeff n]
  exact norm_sum_le _ _

/-- **Every value of a formal block over an Etingof–Schedler-finite VOA is
subexponential.** -/
theorem subexponential_block_of_etingofFinite {S : 𝒱 →ₗ[ℂ] FormalQSeries} {hbase : ℂ}
    (hsupp : ∀ v, S v ∈ QSeriesAt hbase) (hS : IsFormalBlock W S)
    (hzero : VacuumGradeZero W) (hE : EtingofFinite W) (v : 𝒱) :
    Subexponential (fun n : ℕ => ‖S v (hbase + (n : ℂ))‖) :=
  subexponential_block_of_fg W hsupp hS
    (fg_blockSpanS_of_fg hsupp (fg_blockSpan_of_etingofFinite W hsupp hS hzero hE)) v

/-- **The growth datum, from the Etingof–Schedler hypothesis.**  Every module with a
conformal weight over a VOA satisfying `EtingofFinite` has subexponential one-point coefficients.

This is `Modularity.BlockGrowth.onePointSubexp_of_c2` with `C2Cofinite W` weakened to
`EtingofFinite W` — the Arakawa–Kawasetsu improvement, delivered at the exact interface Zhu's
theorem consumes. -/
theorem onePointSubexp_of_etingofFinite {M : Type u} [AddCommGroup M] [Module ℂ M]
    (N : OrdVModule W M) {hw : ℂ} (hcw : HasConformalWeight N hw)
    (hzero : VacuumGradeZero W) (hE : EtingofFinite W) :
    OnePointSubexp N (hw - W.centralCharge / 24) := by
  intro v
  exact subexponential_block_of_etingofFinite W (S := torusOnePointHom N)
    (torusOnePoint_mem_QSeriesAt W N hcw) (torusOnePointHom_isFormalBlock N) hzero hE v

end

/-! ## §7  A witness — nothing here is vacuous

`EtingofFinite_of_C2Cofinite` says every `C₂`-cofinite VOA satisfies the hypothesis, so the
theorems above apply to every VOA Zhu's theorem applies to.  This section instantiates them.

⚠⚠ **The witness situation** (updated).  `C2Cofinite` is proved unconditionally for the trivial
VOA `ℂ𝟙` (`Examples.ZhuInstantiation.trivial_C2Cofinite`), for the Lee–Yang model
(`leeYang_c2Cofinite`, `Examples/LeeYangC2.lean`) and for the lattice triplet `tripletWVOA 2`
(`tripletWVOA_two_c2Cofinite`, `Examples/TripletWpTwoClose.lean`); some older `tripletW2` routes
remain conditional on named hypotheses.  The free boson is a proved *counter*example
(`Examples.HeisenbergC2.heisenberg_not_C2Cofinite`).  This section instantiates the theorems at the
trivial VOA only.

**A witness of strictness exists.**  For `L_{-4/3}(𝔰𝔩₂)`, `EtingofFinite` is proved
unconditionally (`Sl2Pres.etingofFinite_simpleSl2QL'`, `Examples/AffineSl2Presentation.lean`) and
`¬ C2Cofinite` is proved unconditionally (`Sl2NonLisse.not_C2Cofinite_simpleSl2QL`,
`Examples/AffineSl2NonLisse.lean`).  The versions in `Examples.AffineSl2QuasiLisse`
(`etingofFinite_simpleSl2QL`, `QuasiLisseSl2.not_C2Cofinite_simpleSl2QL`) carry redundant
`Sl2Presentation`/`IsExact` hypotheses; note the two `not_C2Cofinite_simpleSl2QL` declarations live
in different namespaces with different hypotheses.
-/

section Witness

variable (W : VertexOperatorAlgebra 𝒱)

/-- The adjoint module's one-point growth, from the Etingof–Schedler hypothesis. -/
theorem onePointSubexp_adjoint_of_etingofFinite (hne : W.vacuum ≠ 0)
    (hzero : VacuumGradeZero W) (hE : EtingofFinite W) :
    OnePointSubexp (adjointModule W) (0 - W.centralCharge / 24) :=
  onePointSubexp_of_etingofFinite W (adjointModule W)
    (adjoint_hasConformalWeight W hne) hzero hE

end Witness

/-- **The trivial VOA satisfies the Etingof–Schedler hypothesis.**  Via
`EtingofFinite_of_C2Cofinite` from `trivial_C2Cofinite`.  ⚠ This is the *only* unconditional
instance available in the repository; see the section note. -/
theorem trivial_etingofFinite : EtingofFinite trivialVOA :=
  EtingofFinite_of_C2Cofinite trivialVOA trivial_C2Cofinite

/-- **Arakawa–Kawasetsu Proposition 5.2, instantiated.**  Non-vacuous: the hypotheses are
discharged, not assumed. -/
theorem trivial_exists_finite_gen_sup_blockRelSpanG :
    ∃ T : Set (𝒱G (LatGen.LatModuleGen (stdLattice 0))), T.Finite ∧
      (⊤ : Submodule (↥GSeries) (𝒱G (LatGen.LatModuleGen (stdLattice 0))))
        = Submodule.span (↥GSeries) T ⊔ blockRelSpanG trivialVOA :=
  exists_finite_gen_sup_blockRelSpanG_of_etingofFinite trivialVOA
    trivial_vacuumGradeZero trivial_etingofFinite

/-- **The growth datum, instantiated.**  The character of the trivial VOA has subexponential
coefficients, obtained through the Arakawa–Kawasetsu route rather than the `C₂` route. -/
theorem trivial_onePointSubexp_adjoint :
    OnePointSubexp (adjointModule trivialVOA) (0 - trivialVOA.centralCharge / 24) :=
  onePointSubexp_adjoint_of_etingofFinite trivialVOA trivialVacuum_ne_zero
    trivial_vacuumGradeZero trivial_etingofFinite

/-! ## §8  Consistency: the new hypothesis really is weaker

Two one-line checks that the generalisation is genuine and that the theorems above are not
vacuously stronger-looking restatements: the spanning hypothesis of §4 is implied by the `C₂` one,
and the growth conclusion of §6 recovers `Modularity.BlockGrowth.onePointSubexp_of_c2`.
-/

section Consistency

variable (W : VertexOperatorAlgebra 𝒱)

/-- A set spanning `𝒱` modulo `O₂` spans it modulo the larger `O₂P` — so
`span_sup_blockRelSpanG_eq_top_of_poisson` implies `span_sup_blockRelSpanG_eq_top` and not
conversely. -/
theorem span_sup_O₂P_eq_top_of_span_sup_O₂ (S : Set 𝒱)
    (htop : (⊤ : Submodule ℂ 𝒱) = Submodule.span ℂ S ⊔ O₂ W) :
    (⊤ : Submodule ℂ 𝒱) = Submodule.span ℂ S ⊔ O₂P W :=
  le_antisymm (htop.le.trans (sup_le_sup_left (O₂_le_O₂P W) _)) le_top

/-- `Modularity.BlockGrowth.onePointSubexp_of_c2`, recovered through the Arakawa–Kawasetsu route.
Nothing is lost by passing to the weaker hypothesis. -/
theorem onePointSubexp_of_c2_via_etingofFinite {M : Type u} [AddCommGroup M] [Module ℂ M]
    (N : OrdVModule W M) {hw : ℂ} (hcw : HasConformalWeight N hw)
    (hzero : VacuumGradeZero W) (hC2 : C2Cofinite W) :
    OnePointSubexp N (hw - W.centralCharge / 24) :=
  onePointSubexp_of_etingofFinite W N hcw hzero (EtingofFinite_of_C2Cofinite W hC2)

end Consistency

end VOA
