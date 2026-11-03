/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Modularity.AKModularODE

/-!
# Arakawa–Kawasetsu Lemma 5.3, **uniformly in the module**

`Modularity.AKModularODE.exists_monic_Lsq_relation_of_etingofFinite` runs its Noetherian chain
*inside* `Submodule.span (↥GSeries) (Set.range (blockRestrict hsupp))`, a submodule of
`↥(QSeriesAt hbase)`.  So the order `s` and the coefficients `G i` it produces are bound *after*
the block `S`, hence depend on the block — and therefore on the module whose character is being
constrained.  The `C₂` twin `Modularity.FormalBlockFinite.exists_monic_Lsq_relation` has the
identical defect.

Arakawa–Kawasetsu do not.  Their Lemma 5.3 produces **one** relation in `V_A`, and the closing
sentence of their Theorem 5.7 — *the space spanned by `χ_M` over all ordinary `M` is a subspace of
the solution space of a single equation* — is only meaningful for a module-independent equation.

This file repairs the order.  The Noetherian argument is run in `𝒱G 𝒱 = A ⊗_ℂ 𝒱` itself, from
`Modules.QuasiLisseFinite.exists_finite_gen_sup_blockRelSpanG_of_etingofFinite` (AK Proposition
5.2, stated upstairs), and the single resulting element of `blockRelSpanG W` is pushed forward
along **every** formal block at once by `Modularity.FormalBlockFinite.blockRelSpanG_le_ker`.

## Main results

* `finComb` — the `R`-linear map `(Fin n → R) →ₗ M`, `f ↦ ∑ i, f i • t i`;
* `exists_monic_relation_mem_of_fin_gen` — pure module theory over a Noetherian ring: if
  `⊤ = span R T ⊔ N` with `T` finite, then any sequence `x : ℕ → M` satisfies a **monic** relation
  `x s − Σ_{i<s} c_i • x i ∈ N` of some order `s ≥ 1`.  The chain is comapped into the free module
  `Fin n → R`, which dodges the quotient `M ⧸ N` entirely;
* `exists_uniform_monic_Lsq_relation_of_fin_gen` — **AK Lemma 5.3 in `V_A`**: a monic
  `L[−2]`-relation modulo `blockRelSpanG W`.  No block, no base `hbase`, no module occurs anywhere
  in the statement;
* `exists_uniform_monic_Lsq_relation_of_etingofFinite`,
  `exists_uniform_monic_Lsq_relation_of_C2Cofinite` — **AK Lemma 5.3, uniform form**: the order `s`
  and the `GSeries` coefficients `G i` are bound *before* `hbase`, `S` and `IsFormalBlock`, and the
  same `s`, `G` work for every formal block simultaneously.  This is the statement
  `Modularity.AKModularODE` and `Modularity.FormalBlockFinite` should have had;
* `formalODE_order_of_monic_of_unitriangular` — the substitution step of AK Theorem 5.7 with the
  order `s` and coefficients `G` taken as **arguments** rather than produced existentially, so a
  uniform `s` can be threaded through it;
* `uniform_order_formalODE_of_etingofFinite_of_sqPrimary`,
  `uniform_order_character_formalODE_of_etingofFinite` — one order `s ≥ 1`, fixed by `W` and
  `a` alone, such that the normalised character of **every** ordinary `W`-module satisfies a monic
  order-`s` linear ODE in `q d/dq` with subexponential coefficients;
* `trivial_uniform_order_character_formalODE` — the main theorem with every hypothesis discharged.

## ⚠⚠ EXACTLY HOW UNIFORM THIS IS — read before quoting it

**The ORDER is module-independent.  The final ODE COEFFICIENTS are NOT.**

`exists_uniform_monic_Lsq_relation_of_etingofFinite` is genuinely uniform: `s` *and* the
`GSeries`-coefficients `G i` of the `L[−2]`-relation are chosen before any block is mentioned, and
one and the same relation is then annihilated by every block.

But the passage from the `L[−2]`-tower to the `q d/dq`-tower runs through AK Lemma 5.5,
`Modularity.AKModularODE.huni_of_sqPrimary`, whose coefficients `hc` are extracted
non-constructively by `Submodule.mem_span_range_iff_exists_fun` from a span membership **inside**
`↥(QSeriesAt hbase)`.  They are therefore block-dependent, and so is
`g' j = hc s j − Σ_{i<s} G i · hc i j`, the coefficient of the final ODE.  AK's own `f_j` depend
only on `(a, Δ, c)`; the ones produced here do not.

So `uniform_order_character_formalODE_of_etingofFinite` says: *there is a single order `s ≥ 1`,
depending only on `W`, such that the normalised character of every ordinary module satisfies* **some**
*monic order-`s` ODE in `q d/dq` with subexponential coefficients.*  It does **not** say that one
single ODE annihilates all of them, and it therefore does **not** yet deliver the closing sentence
of AK Theorem 5.7.

Closing that remaining gap needs a genuinely block-independent Lemma 5.5: an explicit universal
family `U : ℕ → ℕ → PowerSeries ℂ` defined by recursion from `IsFormalBlock.omega` and
`Modularity.AKModularODE.Lsq_tower`, proved to lie in `SubexpPS`, to be unitriangular, and to
satisfy the tower identity for *every* block.  That is a separate piece of work, and it is **not**
done here.

Carried forward unchanged from the header of `Modularity.AKModularODE`: the basis is the Euler
operator `(q d/dq)^i`, not AK's iterated Serre derivative; the coefficient ring is `SubexpPS`, not
`ℂ[G̃₄,G̃₆]`; and **nothing about modularity is proved** — this is not a modular linear
differential equation, and `EtingofFinite` remains an axiomatized hypothesis standing in for
Etingof–Schedler.  The formal-ODE conclusion is near-vacuous (see `Modularity.AKModularODE`).

## Status
Proved, axiom-clean, `pbw`-free, no `sorry`.
-/

namespace VOA

open scoped BigOperators TensorProduct

universe u

/-! ## A Noetherian chain run in a free module, with no quotient -/

/-- The `R`-linear map `(Fin n → R) →ₗ[R] M`, `f ↦ ∑ i, f i • t i`. -/
def finComb {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    {n : ℕ} (t : Fin n → M) : (Fin n → R) →ₗ[R] M where
  toFun f := ∑ i, f i • t i
  map_add' f g := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => add_smul (f i) (g i) (t i))
  map_smul' c f := by
    rw [RingHom.id_apply, Finset.smul_sum]
    exact Finset.sum_congr rfl (fun i _ => by rw [Pi.smul_apply, smul_eq_mul, mul_smul])

@[simp] theorem finComb_apply {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    {n : ℕ} (t : Fin n → M) (f : Fin n → R) : finComb t f = ∑ i, f i • t i := rfl

/-- **A monic relation from a finite spanning family modulo a submodule.**  If `M` is spanned
over a Noetherian ring `R` by a finite set `T` together with a submodule `N`, then every sequence
`x : ℕ → M` satisfies a **monic** relation of some order `s ≥ 1` modulo `N`.

`M ⧸ N` is deliberately never formed.  The chain `D r = span{x₀,…,x_r} ⊔ N` is comapped along
`finComb t : (Fin n → R) →ₗ M`, where `t` is a finite generating family of `span R T`; the free
module `Fin n → R` is Noetherian, so the comapped chain stabilises, and `⊤ = span R T ⊔ N` lets the
stabilisation be pushed back down.  (In the application `M = 𝒱G 𝒱` and the quotient by
`blockRelSpanG W` cannot even be *stated* outside `Modularity.BlockRelSpanG`; see the warning on
`Modules.QuasiLisseFinite.exists_finite_gen_sup_blockRelSpanG_of_etingofFinite`.) -/
theorem exists_monic_relation_mem_of_fin_gen {R : Type*} [CommRing R] [IsNoetherianRing R]
    {M : Type*} [AddCommGroup M] [Module R M] (N : Submodule R M)
    (T : Set M) (hTfin : T.Finite)
    (htop : (⊤ : Submodule R M) = Submodule.span R T ⊔ N) (x : ℕ → M) :
    ∃ (s : ℕ) (c : ℕ → R), 1 ≤ s ∧ (x s - ∑ i ∈ Finset.range s, c i • x i) ∈ N := by
  classical
  obtain ⟨n, t, ht⟩ :=
    Submodule.fg_iff_exists_fin_generating_family.mp (Submodule.fg_span (R := R) hTfin)
  haveI hnoe : IsNoetherian R (Fin n → R) := isNoetherian_pi
  have hDmono : Monotone (fun r : ℕ =>
      Submodule.span R (Set.range (fun i : Fin (r + 1) => x i)) ⊔ N) := by
    intro r r' hrr
    refine sup_le_sup_right (Submodule.span_mono ?_) _
    rintro _ ⟨i, rfl⟩
    exact ⟨⟨i.1, by omega⟩, rfl⟩
  obtain ⟨n₀, hn₀⟩ := monotone_stabilizes_iff_noetherian.mpr hnoe
    ⟨fun r => Submodule.comap (finComb (R := R) t)
        (Submodule.span R (Set.range (fun i : Fin (r + 1) => x i)) ⊔ N),
      fun r r' hrr => Submodule.comap_mono (hDmono hrr)⟩
  have hstab : Submodule.comap (finComb (R := R) t)
      (Submodule.span R (Set.range (fun i : Fin (n₀ + 1) => x i)) ⊔ N)
      = Submodule.comap (finComb (R := R) t)
        (Submodule.span R (Set.range (fun i : Fin (n₀ + 1 + 1) => x i)) ⊔ N) :=
    hn₀ (n₀ + 1) (by omega)
  have hmemtop : x (n₀ + 1) ∈ Submodule.span R T ⊔ N := by rw [← htop]; trivial
  obtain ⟨u, hu, w, hw, huw⟩ := Submodule.mem_sup.mp hmemtop
  have hu' : u ∈ Submodule.span R (Set.range t) := by rw [ht]; exact hu
  obtain ⟨f, hf⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp hu'
  have hψf : finComb (R := R) t f = u := hf
  have hxnext : x (n₀ + 1)
      ∈ Submodule.span R (Set.range (fun i : Fin (n₀ + 1 + 1) => x i)) ⊔ N :=
    Submodule.mem_sup_left (Submodule.subset_span ⟨⟨n₀ + 1, by omega⟩, rfl⟩)
  have huin : u ∈ Submodule.span R (Set.range (fun i : Fin (n₀ + 1 + 1) => x i)) ⊔ N := by
    have hueq : u = x (n₀ + 1) - w := by rw [← huw]; abel
    rw [hueq]
    exact Submodule.sub_mem _ hxnext (Submodule.mem_sup_right hw)
  have hfmem : f ∈ Submodule.comap (finComb (R := R) t)
      (Submodule.span R (Set.range (fun i : Fin (n₀ + 1 + 1) => x i)) ⊔ N) :=
    Submodule.mem_comap.mpr (by rw [hψf]; exact huin)
  rw [← hstab] at hfmem
  have huin0 : u ∈ Submodule.span R (Set.range (fun i : Fin (n₀ + 1) => x i)) ⊔ N := by
    have hmm := Submodule.mem_comap.mp hfmem
    rwa [hψf] at hmm
  have hxin0 : x (n₀ + 1) ∈ Submodule.span R (Set.range (fun i : Fin (n₀ + 1) => x i)) ⊔ N := by
    rw [← huw]
    exact Submodule.add_mem _ huin0 (Submodule.mem_sup_right hw)
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hxin0
  obtain ⟨cc, hcc⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp hy
  refine ⟨n₀ + 1, fun i => if h : i < n₀ + 1 then cc ⟨i, h⟩ else 0, by omega, ?_⟩
  show x (n₀ + 1) - ∑ i ∈ Finset.range (n₀ + 1),
      (if h : i < n₀ + 1 then cc ⟨i, h⟩ else 0) • x i ∈ N
  have hsum : ∑ i ∈ Finset.range (n₀ + 1),
      (if h : i < n₀ + 1 then cc ⟨i, h⟩ else 0) • x i = y := by
    rw [← hcc, ← Fin.sum_univ_eq_sum_range
      (fun i : ℕ => (if h : i < n₀ + 1 then cc ⟨i, h⟩ else 0) • x i) (n₀ + 1)]
    exact Finset.sum_congr rfl (fun i _ => by rw [dif_pos i.2])
  rw [hsum, ← hyz]
  simpa using hz

/-! ## AK Lemma 5.3, in `V_A` -/

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱]

section Uniform

variable (W : VertexOperatorAlgebra 𝒱)

/-- **Arakawa–Kawasetsu Lemma 5.3, in `V_A`.**  Given a finite family `T` spanning
`𝒱G 𝒱 = ℂ[G₂,G₄,G₆] ⊗ 𝒱` modulo the relation module `blockRelSpanG W`, and any vector `a`, the
`L[−2]`-tower over `a` satisfies a **monic** relation of some order `s ≥ 1` with `GSeries`
coefficients, **modulo `blockRelSpanG W`**.

Nothing in the statement mentions a formal block, a base `hbase`, or a module: `blockRelSpanG W`
is a function of `W` alone.  That is the point — `Modularity.FormalBlockFinite.blockRelSpanG_le_ker`
then transports this one relation to *every* block at once.

The hypothesis is the finite spanning datum, not a finiteness hypothesis on `W`, so that the
`C₂`-cofinite route and the Etingof–Schedler route are both corollaries. -/
theorem exists_uniform_monic_Lsq_relation_of_fin_gen
    (T : Set (𝒱G 𝒱)) (hTfin : T.Finite)
    (htop : (⊤ : Submodule (↥GSeries) (𝒱G 𝒱))
      = Submodule.span (↥GSeries) T ⊔ blockRelSpanG W) (a : 𝒱) :
    ∃ (s : ℕ) (c : ℕ → ↥GSeries), 1 ≤ s ∧
      (ιG ((⇑(Lsq W (-2)))^[s] a)
        - ∑ i ∈ Finset.range s, c i • ιG ((⇑(Lsq W (-2)))^[i] a)) ∈ blockRelSpanG W := by
  haveI : IsNoetherianRing (↥GSeries) := isNoetherianRing_GSeries
  exact exists_monic_relation_mem_of_fin_gen (blockRelSpanG W) T hTfin htop
    (fun i => ιG ((⇑(Lsq W (-2)))^[i] a))

/-- **AK Lemma 5.3 in `V_A`, from the Etingof–Schedler hypothesis** (AK Proposition 5.2). -/
theorem exists_uniform_monic_Lsq_relation_mem_of_etingofFinite
    (hzero : VacuumGradeZero W) (hE : EtingofFinite W) (a : 𝒱) :
    ∃ (s : ℕ) (c : ℕ → ↥GSeries), 1 ≤ s ∧
      (ιG ((⇑(Lsq W (-2)))^[s] a)
        - ∑ i ∈ Finset.range s, c i • ιG ((⇑(Lsq W (-2)))^[i] a)) ∈ blockRelSpanG W := by
  obtain ⟨T, hTfin, htop⟩ := exists_finite_gen_sup_blockRelSpanG_of_etingofFinite W hzero hE
  exact exists_uniform_monic_Lsq_relation_of_fin_gen W T hTfin htop a

/-- **AK Lemma 5.3 in `V_A`, from `C₂`-cofiniteness** (Zhu Lemma 4.4.1).  This is the uniform
repair of `Modularity.FormalBlockFinite.exists_monic_Lsq_relation`. -/
theorem exists_uniform_monic_Lsq_relation_mem_of_C2Cofinite
    (hzero : VacuumGradeZero W) (hC2 : C2Cofinite W) (a : 𝒱) :
    ∃ (s : ℕ) (c : ℕ → ↥GSeries), 1 ≤ s ∧
      (ιG ((⇑(Lsq W (-2)))^[s] a)
        - ∑ i ∈ Finset.range s, c i • ιG ((⇑(Lsq W (-2)))^[i] a)) ∈ blockRelSpanG W := by
  classical
  obtain ⟨g, gen, wt, hwt, hgen, hdec⟩ := exists_homog_gen_of_C2Cofinite W hC2
  set Sset : Set 𝒱 := Set.range gen ∪ {W.vacuum} with hSdef
  have hShom : ∀ s ∈ Sset, IsHomog W s := by
    rintro s (⟨i, rfl⟩ | hs)
    · exact ⟨(wt i : ℤ), hgen i⟩
    · rw [Set.mem_singleton_iff] at hs
      exact ⟨0, hs ▸ W.vacuum_mem_grading_zero⟩
  have hSfin : Sset.Finite := (Set.finite_range gen).union (Set.finite_singleton _)
  exact exists_uniform_monic_Lsq_relation_of_fin_gen W ((ιG : 𝒱 →ₗ[ℂ] 𝒱G 𝒱) '' Sset)
    (hSfin.image _) (span_sup_blockRelSpanG_eq_top W hzero Sset hShom hdec) a

/-! ## Pushing the single relation forward along **every** formal block -/

/-- **The uniform pushforward.**  A single monic relation in `V_A` is annihilated by the
`GSeries`-linear lift of *every* formal block, at *every* base, so the same order `s` and the same
`GSeries` coefficients `G i` serve all of them.

Compare `Modularity.FormalBlockFinite.blockRelSpanG_le_ker`, which is the input: the relation
element is produced once, in `V_A`, and only then met with a block. -/
theorem exists_uniform_monic_Lsq_relation_of_relation_mem {s : ℕ} {c : ℕ → ↥GSeries} {a : 𝒱}
    (hmem : (ιG ((⇑(Lsq W (-2)))^[s] a)
      - ∑ i ∈ Finset.range s, c i • ιG ((⇑(Lsq W (-2)))^[i] a)) ∈ blockRelSpanG W)
    {hbase : ℂ} {S : 𝒱 →ₗ[ℂ] FormalQSeries} (hsupp : ∀ v, S v ∈ QSeriesAt hbase)
    (hS : IsFormalBlock W S) :
    S ((⇑(Lsq W (-2)))^[s] a)
      = ∑ i ∈ Finset.range s, psSMul ((c i : PowerSeries ℂ)) (S ((⇑(Lsq W (-2)))^[i] a)) := by
  classical
  have hker := LinearMap.mem_ker.mp (blockRelSpanG_le_ker W hsupp hS hmem)
  rw [map_sub, map_sum] at hker
  simp only [map_smul, blockLift_ιG] at hker
  have heq := eq_of_sub_eq_zero hker
  set π : ↥(QSeriesAt hbase) →+ FormalQSeries :=
    (QSeriesAt hbase).subtype.toAddMonoidHom with hπdef
  have hπr : ∀ v : 𝒱, π (blockRestrict hsupp v) = S v := fun _ => rfl
  have hπs : ∀ (g : ↥GSeries) (z : ↥(QSeriesAt hbase)),
      π (g • z) = psSMul ((g : PowerSeries ℂ)) (π z) := fun _ _ => rfl
  have hcoe := congrArg π heq
  rw [map_sum, hπr] at hcoe
  rw [hcoe]
  exact Finset.sum_congr rfl (fun i _ => by rw [hπs, hπr])

/-- **Arakawa–Kawasetsu Lemma 5.3, uniform form, under the Etingof–Schedler hypothesis.**

Read the binder order: `s` and `G` come **before** `hbase`, `S`, `hsupp` and `IsFormalBlock`.  One
order and one coefficient family, depending only on `W` and `a`, serve the characters of *all*
ordinary modules at once — that is exactly what
`Modularity.AKModularODE.exists_monic_Lsq_relation_of_etingofFinite` does not give, since there the
chain runs inside `↥(QSeriesAt hbase)` and both `s` and `G` are chosen after the block. -/
theorem exists_uniform_monic_Lsq_relation_of_etingofFinite
    (hzero : VacuumGradeZero W) (hE : EtingofFinite W) (a : 𝒱) :
    ∃ (s : ℕ) (G : ℕ → PowerSeries ℂ), 1 ≤ s ∧ (∀ i, G i ∈ GSeries) ∧
      ∀ (hbase : ℂ) (S : 𝒱 →ₗ[ℂ] FormalQSeries) (hsupp : ∀ v, S v ∈ QSeriesAt hbase),
        IsFormalBlock W S →
          S ((⇑(Lsq W (-2)))^[s] a)
            = ∑ i ∈ Finset.range s, psSMul (G i) (S ((⇑(Lsq W (-2)))^[i] a)) := by
  obtain ⟨s, c, hs1, hmem⟩ := exists_uniform_monic_Lsq_relation_mem_of_etingofFinite W hzero hE a
  exact ⟨s, fun i => ((c i : ↥GSeries) : PowerSeries ℂ), hs1, fun i => (c i).2,
    fun _ _ hsupp hS => exists_uniform_monic_Lsq_relation_of_relation_mem W hmem hsupp hS⟩

/-- **Zhu Lemma 4.4.2, uniform form.**  The `C₂`-cofinite twin of the theorem above, and the
repair of `Modularity.FormalBlockFinite.exists_monic_Lsq_relation`: there, `s` and `G` are bound
after the block; here they are bound before it. -/
theorem exists_uniform_monic_Lsq_relation_of_C2Cofinite
    (hzero : VacuumGradeZero W) (hC2 : C2Cofinite W) (a : 𝒱) :
    ∃ (s : ℕ) (G : ℕ → PowerSeries ℂ), 1 ≤ s ∧ (∀ i, G i ∈ GSeries) ∧
      ∀ (hbase : ℂ) (S : 𝒱 →ₗ[ℂ] FormalQSeries) (hsupp : ∀ v, S v ∈ QSeriesAt hbase),
        IsFormalBlock W S →
          S ((⇑(Lsq W (-2)))^[s] a)
            = ∑ i ∈ Finset.range s, psSMul (G i) (S ((⇑(Lsq W (-2)))^[i] a)) := by
  obtain ⟨s, c, hs1, hmem⟩ := exists_uniform_monic_Lsq_relation_mem_of_C2Cofinite W hzero hC2 a
  exact ⟨s, fun i => ((c i : ↥GSeries) : PowerSeries ℂ), hs1, fun i => (c i).2,
    fun _ _ hsupp hS => exists_uniform_monic_Lsq_relation_of_relation_mem W hmem hsupp hS⟩

/-! ## The substitution step, with the order supplied rather than produced -/

set_option maxHeartbeats 1000000 in
-- the double sum swap over `Finset.range s` in a `PowerSeries ℂ`-module is slow to elaborate
/-- **`Modularity.AKModularODE.formalODE_of_monic_of_unitriangular` with `s` and `G` as
arguments.**  The existing version returns `∃ s g, …`, which loses the information that the order
it produces is the order of the monic relation fed in; that makes it impossible to thread a
*uniform* order through.  The proof below is the same substitution, with `s` and `G` bound in the
statement.

⚠ The output coefficients `g` are still block-dependent: they are built from the `hc` of AK
Lemma 5.5, which is extracted from a span membership inside `↥(QSeriesAt hbase)`.  Only the order
`s` is under the caller's control.  See the file header. -/
theorem formalODE_order_of_monic_of_unitriangular {S : 𝒱 →ₗ[ℂ] FormalQSeries} {hbase : ℂ}
    (hsupp : ∀ v, S v ∈ QSeriesAt hbase) (v : 𝒱) (s : ℕ) (G : ℕ → PowerSeries ℂ)
    (hGmem : ∀ i, G i ∈ GSeries)
    (hGrel : S ((⇑(Lsq W (-2)))^[s] v)
      = ∑ i ∈ Finset.range s, psSMul (G i) (S ((⇑(Lsq W (-2)))^[i] v)))
    (huni : ∀ i : ℕ, ∃ hc : ℕ → PowerSeries ℂ,
      (∀ j, hc j ∈ SubexpPS) ∧ hc i = 1 ∧ (∀ j, i < j → hc j = 0) ∧
      S ((⇑(Lsq W (-2)))^[i] v)
        = ∑ j ∈ Finset.range (i + 1), psSMul (hc j) (qDeriv^[j] (S v))) :
    ∃ g : ℕ → ℕ → ℂ, (∀ i, Subexponential (fun k => ‖g i k‖)) ∧
      ∀ e : ℂ, (qDeriv^[s] (S v)) e
        + ∑ i ∈ Finset.range s, qConv (g i) (qDeriv^[i] (S v)) e = 0 := by
  classical
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
  have hL : ∀ i : ℕ, L i = ∑ j ∈ Finset.range (i + 1), (hc i j) • d j := by
    intro i
    refine hinj ?_
    rw [hπL, map_sum, hceq i]
    exact Finset.sum_congr rfl (fun j _ => by rw [hπsmul, hπd])
  have hLext : ∀ i : ℕ, i < s → L i = ∑ j ∈ Finset.range s, (hc i j) • d j := by
    intro i his
    rw [hL i]
    have hsub : Finset.range (i + 1) ⊆ Finset.range s := by
      intro y hy
      rw [Finset.mem_range] at hy ⊢
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
      refine Finset.sum_congr rfl (fun j _ => ?_)
      exact sub_smul (hc s j) (∑ i ∈ Finset.range s, G i * hc i j) (d j)
    rw [hsplit, ← add_sub_assoc, hkey, sub_self]
  have hg'mem : ∀ j, g' j ∈ SubexpPS := by
    intro j
    refine Subalgebra.sub_mem _ (hcmem s j) (Subalgebra.sum_mem _ (fun i _ => ?_))
    exact Subalgebra.mul_mem _ (GSeries_le_subexpPS (hGmem i)) (hcmem i j)
  refine ⟨fun i k => PowerSeries.coeff k (g' i), fun i => hg'mem i, fun e => ?_⟩
  have hcoe := congrArg π hzeroSum
  rw [map_add, map_sum, map_zero, hπd] at hcoe
  rw [Finset.sum_congr rfl (fun j (_ : j ∈ Finset.range s) => by
    rw [hπsmul, hπd])] at hcoe
  have hfun := congrFun hcoe e
  simpa [psSMul] using hfun

/-! ## The ODE with a module-independent **order** -/

/-- **AK Theorem 5.7 equation (2) with a uniform order.**  For a square-bracket primary `a`,
one order `s ≥ 1` — depending only on `W` and `a` — works for every formal block simultaneously.

⚠ Only the order is uniform.  The coefficients `g` are still chosen after the block; see the file
header for exactly why, and for what a block-independent AK Lemma 5.5 would take. -/
theorem uniform_order_formalODE_of_etingofFinite_of_sqPrimary
    (hzero : VacuumGradeZero W) (hE : EtingofFinite W) {a : 𝒱} {Δ : ℂ}
    (ha : IsSqPrimary W a Δ) :
    ∃ s : ℕ, 1 ≤ s ∧
      ∀ (hbase : ℂ) (S : 𝒱 →ₗ[ℂ] FormalQSeries) (hsupp : ∀ v, S v ∈ QSeriesAt hbase),
        IsFormalBlock W S →
          ∃ g : ℕ → ℕ → ℂ, (∀ i, Subexponential (fun k => ‖g i k‖)) ∧
            ∀ e : ℂ, (qDeriv^[s] (S a)) e
              + ∑ i ∈ Finset.range s, qConv (g i) (qDeriv^[i] (S a)) e = 0 := by
  obtain ⟨s, G, hs1, hGmem, hrel⟩ :=
    exists_uniform_monic_Lsq_relation_of_etingofFinite W hzero hE a
  refine ⟨s, hs1, fun hbase S hsupp hS => ?_⟩
  exact formalODE_order_of_monic_of_unitriangular W hsupp a s G hGmem
    (hrel hbase S hsupp hS) (huni_of_sqPrimary W hsupp hS ha)

end Uniform

/-! ## The character of **every** ordinary module, at one and the same order -/

section Character

/-- **One ODE order for all ordinary modules.**  For a VOA satisfying the Etingof–Schedler
hypothesis there is a single order `s ≥ 1`, depending only on `W`, such that the normalised
character `tr_N q^{L₀−c/24}` of **every** ordinary `W`-module `N` with a conformal weight satisfies
a monic linear ODE of order exactly `s` in `q d/dq` with subexponential coefficients.

This is the module-independence that `Modularity.AKModularODE.character_formalODE_of_etingofFinite`
lacks: there `s` is produced after `N`, so the statement is compatible with the order growing
without bound as `N` varies, and the closing sentence of AK Theorem 5.7 is then meaningless.

⚠⚠ **The coefficients still depend on `N`.**  The conclusion is *one order, many equations*, not
*one equation*.  Getting to one equation needs a block-independent AK Lemma 5.5, which this
repository does not have; see the file header.  And, as in `Modularity.AKModularODE`: the basis is
`(q d/dq)^i`, not the iterated Serre derivative; the coefficients are subexponential series, not
elements of `ℂ[G̃₄,G̃₆]`; and nothing whatsoever about modularity is proved.  **This is not AK
Theorem 5.1 and not a modular linear differential equation**, and the conclusion is near-vacuous
(see `Modularity.AKModularODE`). -/
theorem uniform_order_character_formalODE_of_etingofFinite (W : VertexOperatorAlgebra 𝒱)
    (hzero : VacuumGradeZero W) (hE : EtingofFinite W) :
    ∃ s : ℕ, 1 ≤ s ∧
      ∀ {M : Type u} [AddCommGroup M] [Module ℂ M] (N : OrdVModule W M) (hw : ℂ),
        HasConformalWeight N hw →
          ∃ g : ℕ → ℕ → ℂ, (∀ i, Subexponential (fun k => ‖g i k‖)) ∧
            ∀ e : ℂ, (qDeriv^[s] (torusPartition N)) e
              + ∑ i ∈ Finset.range s,
                  qConv (g i) (qDeriv^[i] (torusPartition N)) e = 0 := by
  obtain ⟨s, hs1, hall⟩ := uniform_order_formalODE_of_etingofFinite_of_sqPrimary W hzero hE
    (vacuum_isSqPrimary W)
  refine ⟨s, hs1, ?_⟩
  intro M _ _ N hw hcw
  have hsupp : ∀ v : 𝒱, torusOnePointHom N v ∈ QSeriesAt (hw - W.centralCharge / 24) :=
    fun v => torusOnePoint_mem_QSeriesAt W N hcw v
  have h := hall _ (torusOnePointHom N) hsupp (torusOnePointHom_isFormalBlock N)
  simpa only [torusOnePointHom_apply, torusOnePoint_vacuum] using h

end Character

/-- **The uniform-order theorem with every hypothesis discharged** — so the hypotheses are
satisfiable.  The trivial VOA is already `C₂`-cofinite, so this is a sanity check; a non-trivial
unconditional instance is `Sl2Pres.uniform_order_character_formalODE_simpleSl2QL`
(`Modularity.AKSl2Instance`, at `L₋₄⁄₃(𝔰𝔩₂)`). -/
theorem trivial_uniform_order_character_formalODE :
    ∃ s : ℕ, 1 ≤ s ∧
      ∀ {M : Type} [AddCommGroup M] [Module ℂ M] (N : OrdVModule trivialVOA M) (hw : ℂ),
        HasConformalWeight N hw →
          ∃ g : ℕ → ℕ → ℂ, (∀ i, Subexponential (fun k => ‖g i k‖)) ∧
            ∀ e : ℂ, (qDeriv^[s] (torusPartition N)) e
              + ∑ i ∈ Finset.range s,
                  qConv (g i) (qDeriv^[i] (torusPartition N)) e = 0 :=
  uniform_order_character_formalODE_of_etingofFinite trivialVOA
    trivial_vacuumGradeZero trivial_etingofFinite

end VOA
