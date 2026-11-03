/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Classification.COne.QExpSpan2Residue
import VOA.Classification.COne.QExpKatzLevelOne

/-!
# The trace to level one, grouped by cusps

For `F ∈ M_k(Γ(N))`, `R ∈ M_w(Γ(N))` with `k + w` even, the width-`N` expansion of the level-one
form `Tr(F R)` is

  `Σ_{q ∈ SL₂ℤ/Γ(N)} [qExp(F|q) · qExp(R|q)]^{(0)}`

and the summand is constant on the orbits of `⟨T, -1⟩`. No coset enumeration and no orbit
cardinality is used: the orbit sizes appear only as nonzero natural-number weights.

* `gammaSlash F γ`: the translate `F ∣ γ` (`γ ∈ SL₂ℤ`) as a modular form for `Γ(N)` (normality);
* `qExpansion_trace_eq`: the displayed identity;
* `cuspPsi_smul`: orbit invariance;
* `qExpansion_trace_eq_orbits`: the identity grouped by orbits.
-/

open UpperHalfPlane ModularForm Matrix.SpecialLinearGroup
open scoped MatrixGroups ModularForm Pointwise

noncomputable section

namespace VOA.Classification.COne.SSHecke

/-- `Γ(N)` as a subgroup of `GL₂(ℝ)`. -/
abbrev GammaGL (N : ℕ) : Subgroup (GL (Fin 2) ℝ) := CongruenceSubgroup.Gamma N

theorem mem_GammaGL_iff {N : ℕ} {A : GL (Fin 2) ℝ} :
    A ∈ GammaGL N ↔ ∃ a ∈ CongruenceSubgroup.Gamma N, mapGL ℝ a = A :=
  Subgroup.mem_map

/-- Conjugation by `SL₂ℤ` preserves `Γ(N)` inside `GL₂(ℝ)`. -/
theorem conj_GammaGL (N : ℕ) (γ : SL(2, ℤ)) :
    ConjAct.toConjAct ((mapGL ℝ γ : GL (Fin 2) ℝ)⁻¹) • GammaGL N = GammaGL N := by
  ext A
  rw [map_inv, Subgroup.mem_inv_pointwise_smul_iff, ConjAct.toConjAct_smul]
  constructor
  · rintro hA
    obtain ⟨a, ha, hA'⟩ := mem_GammaGL_iff.mp hA
    refine mem_GammaGL_iff.mpr ⟨γ⁻¹ * a * γ, ?_, ?_⟩
    · simpa using (CongruenceSubgroup.Gamma_normal N).conj_mem a ha γ⁻¹
    · rw [map_mul, map_mul, hA', map_inv]
      group
  · rintro hA
    obtain ⟨a, ha, rfl⟩ := mem_GammaGL_iff.mp hA
    refine mem_GammaGL_iff.mpr ⟨γ * a * γ⁻¹, ?_, ?_⟩
    · exact (CongruenceSubgroup.Gamma_normal N).conj_mem a ha γ
    · rw [map_mul, map_mul, map_inv]

/-- The translate `F ∣ γ` as a modular form for `Γ(N)`. -/
def gammaSlash {N : ℕ} {k : ℤ} (F : ModularForm (GammaGL N) k) (γ : SL(2, ℤ)) :
    ModularForm (GammaGL N) k :=
  ModularForm.mcast rfl (ModularForm.translate F (mapGL ℝ γ : GL (Fin 2) ℝ))
    (conj_GammaGL N γ).symm

theorem coe_gammaSlash {N : ℕ} {k : ℤ} (F : ModularForm (GammaGL N) k) (γ : SL(2, ℤ)) :
    ⇑(gammaSlash F γ) = ⇑F ∣[k] γ := by
  rfl

theorem gammaSlash_mul_apply {N : ℕ} {k w : ℤ} (F : ModularForm (GammaGL N) k)
    (R : ModularForm (GammaGL N) w) (γ : SL(2, ℤ)) :
    ⇑(gammaSlash (F.mul R) γ) = ⇑((gammaSlash F γ).mul (gammaSlash R γ)) := by
  rw [coe_gammaSlash, ModularForm.coe_mul, ModularForm.coe_mul, coe_gammaSlash,
    coe_gammaSlash, ModularForm.mul_slash_SL2]

theorem gammaSlash_slash {N : ℕ} {k : ℤ} (F : ModularForm (GammaGL N) k) (γ δ : SL(2, ℤ)) :
    ⇑(gammaSlash F (γ * δ)) = ⇑(gammaSlash F γ) ∣[k] δ := by
  rw [coe_gammaSlash, coe_gammaSlash, SlashAction.slash_mul]

/-! ## Cosets and representatives -/

/-- The coset space `SL₂ℤ / Γ(N)` used by Mathlib's trace. -/
abbrev CosetQ (N : ℕ) := ↥𝒮ℒ ⧸ (GammaGL N).subgroupOf 𝒮ℒ

theorem exists_cosetRep {N : ℕ} (q : CosetQ N) :
    ∃ γ : SL(2, ℤ), mapGL ℝ γ = ((q.out : ↥𝒮ℒ) : GL (Fin 2) ℝ)⁻¹ :=
  MonoidHom.mem_range.mp (inv_mem (q.out : ↥𝒮ℒ).2)

/-- An `SL₂ℤ` matrix representing `q.out⁻¹`. -/
def cosetRep {N : ℕ} (q : CosetQ N) : SL(2, ℤ) := (exists_cosetRep q).choose

theorem mapGL_cosetRep {N : ℕ} (q : CosetQ N) :
    mapGL ℝ (cosetRep q) = ((q.out : ↥𝒮ℒ) : GL (Fin 2) ℝ)⁻¹ :=
  (exists_cosetRep q).choose_spec

theorem quotientFunc_eq_gammaSlash {N : ℕ} {k : ℤ} (F : ModularForm (GammaGL N) k)
    (q : CosetQ N) :
    SlashInvariantForm.quotientFunc F q = ⇑(gammaSlash F (cosetRep q)) := by
  conv_lhs => rw [← Quotient.out_eq q]
  rw [coe_gammaSlash, ModularForm.SL_slash]
  change SlashInvariantForm.quotientFunc F ⟦q.out⟧ = _
  rw [SlashInvariantForm.quotientFunc_mk]
  congr 1
  exact (mapGL_cosetRep q).symm

/-- The identity coset. -/
def cosetOne (N : ℕ) : CosetQ N := ⟦(1 : ↥𝒮ℒ)⟧

theorem quotientFunc_cosetOne {N : ℕ} {k : ℤ} (F : ModularForm (GammaGL N) k) :
    SlashInvariantForm.quotientFunc F (cosetOne N) = ⇑F := by
  rw [cosetOne, SlashInvariantForm.quotientFunc_mk]
  simp

/-! ## Expansions -/

theorem nat_mem_strictPeriods_SL (N : ℕ) : (N : ℝ) ∈ (𝒮ℒ).strictPeriods := by
  simpa using (𝒮ℒ).strictPeriods.nsmul_mem one_mem_strictPeriods_SL N

theorem hasSum_qExpansion_Gamma {N : ℕ} [NeZero N] {k : ℤ}
    (F : ModularForm (GammaGL N) k) (τ : ℍ) :
    HasSum (fun n => (qExpansion (N : ℝ) F).coeff n •
      Function.Periodic.qParam (N : ℝ) τ ^ n) (F τ) :=
  hasSum_qExpansion (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N))
    (SlashInvariantFormClass.periodic_comp_ofComplex F (nat_mem_strictPeriods_Gamma N))
    (ModularFormClass.holo F) (ModularFormClass.bdd_at_infty F) τ

/-- Width-`N` expansion of a level-one form inserts zeros. -/
theorem qExpansion_levelOne_nat {N : ℕ} (hN : 0 < N) {k : ℤ} (G : ModularForm 𝒮ℒ k) :
    qExpansion (N : ℝ) G = PowerSeries.expand N hN.ne' (qExpansion 1 G) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hinj : Function.Injective (fun n : ℕ => N * n) := mul_right_injective₀ hN.ne'
  have hsum (τ : ℍ) : HasSum
      (fun n => (PowerSeries.expand N hN.ne' (qExpansion 1 G)).coeff n •
        Function.Periodic.qParam (N : ℝ) τ ^ n) (G τ) := by
    apply (hinj.hasSum_iff ?_).mp
    · simpa only [Function.comp_def, PowerSeries.coeff_expand_mul, pow_mul,
        qParam_nat_pow hN] using
        hasSum_qExpansion one_pos
          (SlashInvariantFormClass.periodic_comp_ofComplex G one_mem_strictPeriods_SL)
          (ModularFormClass.holo G) (ModularFormClass.bdd_at_infty G) τ
    · intro n hn
      have hnd : ¬ N ∣ n := by
        rintro ⟨j, rfl⟩
        exact hn ⟨j, rfl⟩
      rw [PowerSeries.coeff_expand_of_not_dvd N hN.ne' _ hnd, zero_smul]
  ext n
  exact (ModularFormClass.qExpansion_coeff_unique hNR (nat_mem_strictPeriods_SL N) hsum n).symm

/-- Level-one forms have finite coefficient lattices at width `N` too. -/
theorem levelOne_nat_hasFiniteCoeffLattice {N : ℕ} (hN : 0 < N) {k : ℤ}
    (G : ModularForm 𝒮ℒ k) :
    ∃ L : Submodule ℤ ℂ, L.FG ∧ ∀ n, (qExpansion (N : ℝ) G).coeff n ∈ L := by
  obtain ⟨L, hL, hc⟩ := levelOne_hasFiniteCoeffLattice k G
  refine ⟨L, hL, fun n => ?_⟩
  rw [qExpansion_levelOne_nat hN]
  by_cases hd : N ∣ n
  · obtain ⟨j, rfl⟩ := hd
    rw [PowerSeries.coeff_expand_mul]
    exact hc j
  · rw [PowerSeries.coeff_expand_of_not_dvd N hN.ne' _ hd]
    exact L.zero_mem

/-! ## The trace expansion -/

instance cosetQFintype (N : ℕ) [NeZero N] : Fintype (CosetQ N) := Fintype.ofFinite _

/-- The cusp summand `[qExp(P ∣ q)]^{(0)}`. -/
def cuspPsi {N : ℕ} {k : ℤ} (P : ModularForm (GammaGL N) k) (q : CosetQ N) :
    PowerSeries ℂ :=
  resPart N 0 (qExpansion (N : ℝ) (gammaSlash P (cosetRep q)))

theorem coeff_qExpansion_trace {N : ℕ} [NeZero N] {k : ℤ}
    (P : ModularForm (GammaGL N) k) (n : ℕ) :
    (qExpansion (N : ℝ) (ModularForm.trace 𝒮ℒ P)).coeff n =
      ∑ q : CosetQ N, (qExpansion (N : ℝ) (gammaSlash P (cosetRep q))).coeff n := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  refine (ModularFormClass.qExpansion_coeff_unique hNR (nat_mem_strictPeriods_SL N)
    (c := fun n => ∑ q : CosetQ N, (qExpansion (N : ℝ) (gammaSlash P (cosetRep q))).coeff n)
    (f := ModularForm.trace 𝒮ℒ P) (fun τ => ?_) n).symm
  have hT : (ModularForm.trace 𝒮ℒ P) τ =
      ∑ q : CosetQ N, (gammaSlash P (cosetRep q)) τ := by
    rw [ModularForm.coe_trace, Finset.sum_apply]
    convert Finset.sum_congr rfl fun q _ => congrFun (quotientFunc_eq_gammaSlash P q) τ
  rw [hT]
  have := hasSum_sum (s := (Finset.univ : Finset (CosetQ N)))
    fun q _ => hasSum_qExpansion_Gamma (gammaSlash P (cosetRep q)) τ
  simpa only [Finset.sum_smul] using this

/-- The width-`N` expansion of the trace is the sum of the cusp summands. -/
theorem qExpansion_trace_eq {N : ℕ} [NeZero N] {k : ℤ} (P : ModularForm (GammaGL N) k) :
    qExpansion (N : ℝ) (ModularForm.trace 𝒮ℒ P) = ∑ q : CosetQ N, cuspPsi P q := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  ext n
  rw [map_sum]
  simp only [cuspPsi, coeff_resPart]
  by_cases hn : n % N = 0 % N
  · simp only [if_pos hn]
    exact coeff_qExpansion_trace P n
  · simp only [if_neg hn, Finset.sum_const_zero]
    rw [qExpansion_levelOne_nat hN, PowerSeries.coeff_expand_of_not_dvd N hN.ne']
    rw [Nat.zero_mod] at hn
    exact fun h => hn (Nat.mod_eq_zero_of_dvd h)

/-! ## Orbits of `⟨T, -1⟩` -/

/-- `SL₂ℤ → 𝒮ℒ`. -/
def slHom : SL(2, ℤ) →* ↥𝒮ℒ := (mapGL ℝ).rangeRestrict

theorem coe_slHom (x : SL(2, ℤ)) : ((slHom x : ↥𝒮ℒ) : GL (Fin 2) ℝ) = mapGL ℝ x := rfl

/-- The subgroup `⟨T⁻¹, -1⟩ ⊂ SL₂ℤ`. -/
def cuspStab : Subgroup SL(2, ℤ) :=
  Subgroup.closure {ModularGroup.T⁻¹, -1}

/-- Its image acting on cosets. -/
def cuspStabGL : Subgroup ↥𝒮ℒ := cuspStab.map slHom

/-- The cusps of `Γ(N)`, as orbits of `⟨T, -1⟩` on `SL₂ℤ / Γ(N)`. -/
abbrev CuspOrb (N : ℕ) := MulAction.orbitRel.Quotient cuspStabGL (CosetQ N)

theorem quotientFunc_slHom_smul {N : ℕ} {k : ℤ} (P : ModularForm (GammaGL N) k)
    (x : SL(2, ℤ)) (q : CosetQ N) :
    SlashInvariantForm.quotientFunc P (slHom x • q) =
      ⇑(gammaSlash P (cosetRep q * x⁻¹)) := by
  have h := SlashInvariantForm.quotientFunc_smul P (slHom x⁻¹).2 q
  have hx : (⟨((slHom x⁻¹ : ↥𝒮ℒ) : GL (Fin 2) ℝ), (slHom x⁻¹).2⟩ : ↥𝒮ℒ)⁻¹ = slHom x := by
    rw [Subtype.coe_eta, ← map_inv, inv_inv]
  rw [hx] at h
  rw [← h, quotientFunc_eq_gammaSlash, gammaSlash_slash]
  rfl

theorem qExpansion_gammaSlash_cosetRep_smul {N : ℕ} {k : ℤ} (P : ModularForm (GammaGL N) k)
    (x : SL(2, ℤ)) (q : CosetQ N) :
    qExpansion (N : ℝ) (gammaSlash P (cosetRep (slHom x • q))) =
      qExpansion (N : ℝ) (gammaSlash P (cosetRep q * x⁻¹)) := by
  rw [← quotientFunc_eq_gammaSlash, quotientFunc_slHom_smul]

theorem qParam_add_one (N : ℕ) (τ : ℍ) :
    Function.Periodic.qParam (N : ℝ) (((1 : ℝ) +ᵥ τ : ℍ) : ℂ) =
      weightOneStandardRoot N * Function.Periodic.qParam (N : ℝ) τ := by
  rw [UpperHalfPlane.coe_vadd]
  simp only [Function.Periodic.qParam, weightOneStandardRoot, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Translation by `T` twists the `n`-th coefficient by `ζ^n`. -/
theorem coeff_qExpansion_gammaSlash_mul_T {N : ℕ} [NeZero N] {k : ℤ}
    (P : ModularForm (GammaGL N) k) (γ : SL(2, ℤ)) (n : ℕ) :
    (qExpansion (N : ℝ) (gammaSlash P (γ * ModularGroup.T))).coeff n =
      weightOneStandardRoot N ^ n * (qExpansion (N : ℝ) (gammaSlash P γ)).coeff n := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  refine (ModularFormClass.qExpansion_coeff_unique hNR (nat_mem_strictPeriods_Gamma N)
    (c := fun n => weightOneStandardRoot N ^ n *
      (qExpansion (N : ℝ) (gammaSlash P γ)).coeff n)
    (f := gammaSlash P (γ * ModularGroup.T)) (fun τ => ?_) n).symm
  have hf : (gammaSlash P (γ * ModularGroup.T)) τ = (gammaSlash P γ) ((1 : ℝ) +ᵥ τ) := by
    rw [gammaSlash_slash, ModularForm.SL_slash_apply, UpperHalfPlane.modular_T_smul]
    simp [UpperHalfPlane.denom, ModularGroup.T]
  rw [hf]
  have := hasSum_qExpansion_Gamma (gammaSlash P γ) ((1 : ℝ) +ᵥ τ)
  rw [qParam_add_one] at this
  convert this using 2 with m
  simp only [smul_eq_mul, mul_pow]
  ring

/-- `-1` acts trivially in even weight. -/
theorem gammaSlash_mul_neg_one {N : ℕ} {k : ℤ} (hk : Even k)
    (P : ModularForm (GammaGL N) k) (γ : SL(2, ℤ)) :
    ⇑(gammaSlash P (γ * -1)) = ⇑(gammaSlash P γ) := by
  rw [gammaSlash_slash]
  funext τ
  rw [ModularForm.SL_slash_apply]
  have h1 : ((-1 : SL(2, ℤ)) • τ) = τ := by
    rw [ModularGroup.SL_neg_smul, one_smul]
  have h2 : UpperHalfPlane.denom (-1 : SL(2, ℤ)) τ = -1 := by
    simp [UpperHalfPlane.denom]
  rw [h1, h2, hk.neg.neg_one_zpow, mul_one]

/-- The orbit invariance of the cusp summand. -/
theorem cuspPsi_slHom_smul {N : ℕ} [NeZero N] {k : ℤ} (hk : Even k)
    (P : ModularForm (GammaGL N) k) {x : SL(2, ℤ)} (hx : x ∈ cuspStab) (q : CosetQ N) :
    cuspPsi P (slHom x • q) = cuspPsi P q := by
  let S : Subgroup SL(2, ℤ) :=
    { carrier := {x | ∀ q : CosetQ N, cuspPsi P (slHom x • q) = cuspPsi P q}
      mul_mem' := by
        intro a b ha hb q
        rw [map_mul, mul_smul, ha, hb]
      one_mem' := by intro q; rw [map_one, one_smul]
      inv_mem' := by
        intro a ha q
        conv_rhs => rw [← smul_inv_smul (slHom a) q]
        rw [ha, map_inv] }
  have hle : cuspStab ≤ S := by
    rw [cuspStab, Subgroup.closure_le]
    rintro x (rfl | rfl) q
    · simp only [cuspPsi]
      rw [qExpansion_gammaSlash_cosetRep_smul, inv_inv]
      ext n
      rw [coeff_resPart, coeff_resPart, coeff_qExpansion_gammaSlash_mul_T]
      split_ifs with hn
      · rw [Nat.zero_mod] at hn
        obtain ⟨j, rfl⟩ := Nat.dvd_of_mod_eq_zero hn
        have hz : weightOneStandardRoot N ^ N = 1 :=
          (Complex.isPrimitiveRoot_exp N (NeZero.ne N)).pow_eq_one
        rw [pow_mul, hz, one_pow, one_mul]
      · rfl
    · simp only [cuspPsi]
      rw [qExpansion_gammaSlash_cosetRep_smul, inv_neg_one, gammaSlash_mul_neg_one hk]
  exact hle hx q

/-- Every element of a `⟨T,-1⟩`-orbit has the same cusp summand. -/
theorem cuspPsi_eq_of_orbit {N : ℕ} [NeZero N] {k : ℤ} (hk : Even k)
    (P : ModularForm (GammaGL N) k) {q q' : CosetQ N}
    (h : (⟦q⟧ : CuspOrb N) = ⟦q'⟧) : cuspPsi P q = cuspPsi P q' := by
  have h' : q ∈ MulAction.orbit cuspStabGL q' := MulAction.orbitRel_apply.mp (Quotient.exact h)
  rw [MulAction.mem_orbit_iff] at h'
  obtain ⟨⟨g, hg⟩, rfl⟩ := h'
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hg
  exact cuspPsi_slHom_smul hk P hx q'

instance cuspOrbFintype (N : ℕ) [NeZero N] : Fintype (CuspOrb N) := Fintype.ofFinite _

open scoped Classical in
/-- **The trace grouped by cusps.** For any choice of representatives. -/
theorem qExpansion_trace_eq_orbits {N : ℕ} [NeZero N] {k : ℤ} (hk : Even k)
    (P : ModularForm (GammaGL N) k) (rep : CuspOrb N → CosetQ N)
    (hrep : ∀ O, (⟦rep O⟧ : CuspOrb N) = O) :
    qExpansion (N : ℝ) (ModularForm.trace 𝒮ℒ P) =
      ∑ O : CuspOrb N,
        ((Finset.univ.filter fun q : CosetQ N => (⟦q⟧ : CuspOrb N) = O).card : ℂ) •
          cuspPsi P (rep O) := by
  classical
  rw [qExpansion_trace_eq, ← Finset.sum_fiberwise Finset.univ
    (fun q : CosetQ N => (⟦q⟧ : CuspOrb N))]
  refine Finset.sum_congr rfl fun O _ => ?_
  rw [Finset.sum_congr rfl (g := fun _ => cuspPsi P (rep O)), Finset.sum_const,
    Nat.cast_smul_eq_nsmul]
  intro q hq
  rw [Finset.mem_filter] at hq
  exact cuspPsi_eq_of_orbit hk P (hq.2.trans (hrep O).symm)

end VOA.Classification.COne.SSHecke
