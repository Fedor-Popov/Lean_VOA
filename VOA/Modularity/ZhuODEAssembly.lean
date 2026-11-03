/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modularity.QDerivProductRule

/-!
# Residual **(c)**, assembled: the monic ODE from Zhu 4.4.2 + Zhu 4.4.4

`Modularity.FormalBlockFinite.exists_monic_Lsq_relation` (Zhu Lemma 4.4.2) gives a **monic**
relation among the `S(L[−2]^i v)` with `GSeries` coefficients.  Zhu Lemma 4.4.4 converts the
`L[−2]`-tower into the `q d/dq`-tower **unitriangularly**.  This file performs the substitution: the
two together give exactly the hypothesis of
`Modularity.FormalODE.onePointSubexp_of_formalODE`, and hence the growth datum.

Unitriangularity is what preserves monicity, and monicity is what fixes `deg P = s ≥ 1` in the
indicial polynomial downstream.  The conversion coefficients are only required to be
**subexponential**, not to lie in a finitely generated ring — see
`Modularity.QDerivProductRule` for why that removes the need for Ramanujan's identities.

## Main results

* `qDeriv_iterate_mem_QSeriesAt`;
* `formalODE_of_unitriangular` — Zhu 4.4.2 + Zhu 4.4.4 ⟹ the monic formal ODE;
* `onePointSubexp_of_unitriangular` — hence `OnePointSubexp`, i.e. residual **(c)**, from the
  single remaining input (Zhu Lemma 4.4.4).

## Status
Proved, axiom-clean, `pbw`-free, no `sorry`.
-/

namespace VOA

open scoped BigOperators

universe u

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

theorem qDeriv_iterate_mem_QSeriesAt {h : ℂ} {χ : FormalQSeries} (hχ : χ ∈ QSeriesAt h) (j : ℕ) :
    (qDeriv^[j] χ) ∈ QSeriesAt h := by
  induction j with
  | zero => simpa using hχ
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact qDeriv_mem_QSeriesAt ih

section Assembly

variable (W : VertexOperatorAlgebra 𝒱)

set_option maxHeartbeats 1000000 in
/-- **The monic formal ODE.**  Zhu Lemma 4.4.2 (banked: `exists_monic_Lsq_relation`) supplies
a monic relation in the `L[−2]`-tower with `GSeries` coefficients; the hypothesis `huni` is Zhu
Lemma 4.4.4 — the **unitriangular** conversion of the `L[−2]`-tower into the `q d/dq`-tower with
subexponential coefficients.  Substituting one into the other gives the monic ODE. -/
theorem formalODE_of_unitriangular {S : 𝒱 →ₗ[ℂ] FormalQSeries} {hbase : ℂ}
    (hsupp : ∀ v, S v ∈ QSeriesAt hbase) (hS : IsFormalBlock W S)
    (hzero : VacuumGradeZero W) (hC2 : C2Cofinite W) (v : 𝒱)
    (huni : ∀ i : ℕ, ∃ hc : ℕ → PowerSeries ℂ,
      (∀ j, hc j ∈ SubexpPS) ∧ hc i = 1 ∧ (∀ j, i < j → hc j = 0) ∧
      S ((⇑(Lsq W (-2)))^[i] v)
        = ∑ j ∈ Finset.range (i + 1), psSMul (hc j) (qDeriv^[j] (S v))) :
    ∃ (s : ℕ) (g : ℕ → ℕ → ℂ), 1 ≤ s ∧ (∀ i, Subexponential (fun k => ‖g i k‖)) ∧
      ∀ e : ℂ, (qDeriv^[s] (S v)) e
        + ∑ i ∈ Finset.range s, qConv (g i) (qDeriv^[i] (S v)) e = 0 := by
  classical
  obtain ⟨s, G, hs1, hGmem, hGrel⟩ := exists_monic_Lsq_relation W hsupp hS hzero hC2 v
  choose hc hcmem hcone hczero hceq using huni
  set d : ℕ → ↥(QSeriesAt hbase) := fun j =>
    ⟨qDeriv^[j] (S v), qDeriv_iterate_mem_QSeriesAt (hsupp v) j⟩ with hd
  set L : ℕ → ↥(QSeriesAt hbase) := fun i =>
    ⟨S ((⇑(Lsq W (-2)))^[i] v), hsupp _⟩ with hLdef
  set π : ↥(QSeriesAt hbase) →+ FormalQSeries :=
    (QSeriesAt hbase).subtype.toAddMonoidHom with hπ
  have hπd : ∀ j : ℕ, π (d j) = qDeriv^[j] (S v) := fun _ => rfl
  have hπL : ∀ i : ℕ, π (L i) = S ((⇑(Lsq W (-2)))^[i] v) := fun _ => rfl
  have hπsmul : ∀ (F : PowerSeries ℂ) (y : ↥(QSeriesAt hbase)),
      π (F • y) = psSMul F (π y) := fun _ _ => rfl
  have hinj : Function.Injective π := fun a b hab => Subtype.ext hab
  -- the unitriangular expansion, transported into the module
  have hL : ∀ i : ℕ, L i = ∑ j ∈ Finset.range (i + 1), (hc i j) • d j := by
    intro i
    refine hinj ?_
    rw [hπL, map_sum, hceq i]
    exact Finset.sum_congr rfl (fun j _ => by rw [hπsmul, hπd])
  have hLext : ∀ i : ℕ, i < s → L i = ∑ j ∈ Finset.range s, (hc i j) • d j := by
    intro i his
    rw [hL i]
    have hsub : Finset.range (i + 1) ⊆ Finset.range s := by
      intro x hx
      rw [Finset.mem_range] at hx ⊢
      omega
    refine Finset.sum_subset hsub ?_
    intro j hjs hj
    rw [Finset.mem_range] at hjs
    rw [Finset.mem_range] at hj
    have hij : i < j := by omega
    rw [hczero i j hij, zero_smul]
  have hrel : L s = ∑ i ∈ Finset.range s, (G i) • L i := by
    refine hinj ?_
    rw [hπL, map_sum, hGrel]
    exact Finset.sum_congr rfl (fun i _ => by rw [hπsmul, hπL])
  have hLHS : L s = d s + ∑ j ∈ Finset.range s, (hc s j) • d j := by
    rw [hL s, Finset.sum_range_succ, hcone s, one_smul, add_comm]
  have hRHS : ∑ i ∈ Finset.range s, (G i) • L i
      = ∑ j ∈ Finset.range s, (∑ i ∈ Finset.range s, G i * hc i j) • d j := by
    rw [Finset.sum_congr rfl (fun i hi => by
      rw [hLext i (Finset.mem_range.mp hi), Finset.smul_sum])]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.sum_smul]
    exact Finset.sum_congr rfl (fun i _ => (mul_smul (G i) (hc i j) (d j)).symm)
  set g' : ℕ → PowerSeries ℂ :=
    fun j => hc s j - ∑ i ∈ Finset.range s, G i * hc i j with hg'
  have hzeroSum : d s + ∑ j ∈ Finset.range s, (g' j) • d j = 0 := by
    have hkey : d s + ∑ j ∈ Finset.range s, (hc s j) • d j
        = ∑ j ∈ Finset.range s, (∑ i ∈ Finset.range s, G i * hc i j) • d j := by
      rw [← hLHS, hrel, hRHS]
    have hsplit : ∑ j ∈ Finset.range s, (g' j) • d j
        = (∑ j ∈ Finset.range s, (hc s j) • d j)
          - ∑ j ∈ Finset.range s, (∑ i ∈ Finset.range s, G i * hc i j) • d j := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun j _ => by rw [hg', sub_smul])
    rw [hsplit, ← add_sub_assoc, hkey, sub_self]
  have hg'mem : ∀ j, g' j ∈ SubexpPS := by
    intro j
    refine Subalgebra.sub_mem _ (hcmem s j) (Subalgebra.sum_mem _ (fun i _ => ?_))
    exact Subalgebra.mul_mem _ (GSeries_le_subexpPS (hGmem i)) (hcmem i j)
  refine ⟨s, fun i k => PowerSeries.coeff k (g' i), hs1, fun i => hg'mem i, fun e => ?_⟩
  have hcoe := congrArg π hzeroSum
  rw [map_add, map_sum, map_zero, hπd] at hcoe
  rw [Finset.sum_congr rfl (fun j (_ : j ∈ Finset.range s) => by
    rw [hπsmul, hπd])] at hcoe
  have hfun := congrFun hcoe e
  simpa [psSMul] using hfun

/-- **Residual (c), reduced to Zhu Lemma 4.4.4.**  Given the unitriangular conversion, the
growth datum `OnePointSubexp` follows for every module.

⚠ **Refuted hypothesis — this theorem is vacuous for essentially every module.** `huni`, quantified
over *all* `v`, is false whenever some `𝒵(L[−3]x) ≠ 0`: at `i = 1`, `v = L[−1]x` it forces
`torusOnePoint N (Lsq W (-3) x) = 0` (`torusOnePoint_Lsq_neg_three_eq_zero_of_uniStep`,
`Modularity/UniCollapse.lean`). Zhu's Lemma 4.4.4 holds only for square-bracket primary `v`.
Kept as a recorded dead end; nothing in the library consumes it. The
growth datum is proved unconditionally from `C₂`-cofiniteness by `onePointSubexp_of_c2`.
`VacuumGradeZero` is not a hypothesis (it holds for every VOA, `vacuumGradeZero_holds`). -/
theorem onePointSubexp_of_unitriangular {M : Type u} [AddCommGroup M] [Module ℂ M]
    (N : OrdVModule W M) (hbase : ℂ)
    (hsupp0 : OnePointSupported N hbase)
    (hsupp : ∀ v : 𝒱, torusOnePoint N v ∈ QSeriesAt hbase)
    (hC2 : C2Cofinite W)
    (huni : ∀ (v : 𝒱) (i : ℕ), ∃ hc : ℕ → PowerSeries ℂ,
      (∀ j, hc j ∈ SubexpPS) ∧ hc i = 1 ∧ (∀ j, i < j → hc j = 0) ∧
      torusOnePoint N ((⇑(Lsq W (-2)))^[i] v)
        = ∑ j ∈ Finset.range (i + 1),
            psSMul (hc j) (qDeriv^[j] (torusOnePoint N v))) :
    OnePointSubexp N hbase :=
  onePointSubexp_of_formalODE N hbase hsupp0 (fun v =>
    formalODE_of_unitriangular W (S := torusOnePointHom N) hsupp
      (torusOnePointHom_isFormalBlock N) (vacuumGradeZero_holds W) hC2 v (huni v))

/-- The one-point functions of a module with a conformal weight are supported on `hbase + ℕ` — the
full off-coset strengthening of `onePointSupported_of_hasConformalWeight`, which is what the
`PowerSeries ℂ`-module structure of `QSeriesAt` requires. -/
theorem torusOnePoint_mem_QSeriesAt {M : Type u} [AddCommGroup M] [Module ℂ M]
    (N : OrdVModule W M) {hw : ℂ} (hcw : HasConformalWeight N hw) (v : 𝒱) :
    torusOnePoint N v ∈ QSeriesAt (hw - W.centralCharge / 24) := by
  intro e he
  refine gradedTraceOp_eq_zero_of_weight_bot N (oMod N v) _ ?_
  by_contra hbot
  obtain ⟨n, hn⟩ := hcw.2 _ hbot
  exact he n (by linear_combination hn)

/-- **Residual (c), reduced to a single statement.**  For a `C₂`-cofinite VOA and a module
with a conformal weight, the growth datum `OnePointSubexp` — the `hgr` hypothesis of the modularity
theorem — follows from **Zhu Lemma 4.4.4 alone**: the unitriangular conversion of the `L[−2]`-tower
into the `q d/dq`-tower with subexponential coefficients.

⚠ **Refuted hypothesis — this theorem is vacuous for essentially every module.** `huni`, quantified
over *all* `v`, is false whenever some `𝒵(L[−3]x) ≠ 0`: at `i = 1`, `v = L[−1]x` it forces
`torusOnePoint N (Lsq W (-3) x) = 0` (`torusOnePoint_Lsq_neg_three_eq_zero_of_uniStep`,
`Modularity/UniCollapse.lean`). Zhu's Lemma 4.4.4 holds only for square-bracket primary `v`.
Kept as a recorded dead end; nothing in the library consumes it. The
growth datum is proved unconditionally from `C₂`-cofiniteness by `onePointSubexp_of_c2`.
`VacuumGradeZero` is not a hypothesis (it holds for every VOA, `vacuumGradeZero_holds`). -/
theorem onePointSubexp_of_unitriangular_cw {M : Type u} [AddCommGroup M] [Module ℂ M]
    (N : OrdVModule W M) {hw : ℂ} (hcw : HasConformalWeight N hw)
    (hC2 : C2Cofinite W)
    (huni : ∀ (v : 𝒱) (i : ℕ), ∃ hc : ℕ → PowerSeries ℂ,
      (∀ j, hc j ∈ SubexpPS) ∧ hc i = 1 ∧ (∀ j, i < j → hc j = 0) ∧
      torusOnePoint N ((⇑(Lsq W (-2)))^[i] v)
        = ∑ j ∈ Finset.range (i + 1),
            psSMul (hc j) (qDeriv^[j] (torusOnePoint N v))) :
    OnePointSubexp N (hw - W.centralCharge / 24) :=
  onePointSubexp_of_unitriangular W N _ (onePointSupported_of_hasConformalWeight N hcw)
    (torusOnePoint_mem_QSeriesAt W N hcw) hC2 huni

end Assembly

end VOA
