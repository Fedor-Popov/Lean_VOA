/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.Filtered.VirasoroWordLi
import VOA.Filtered.GeneratorWordLiSurjectivity
import VOA.Filtered.ArcBaseExactness
import VOA.Examples.TwoSeriesDSVirSymbol
import VOA.Commutative.InfiniteJetGenerators

/-!
# Intrinsic Li classical freeness of the Virasoro minimal models `M(2, 2n+1)`

Let `L = L(c_{2,2n+1}, 0)` be the simple Virasoro VOA (`virasoroSimple`, the quotient of the
universal vacuum VOA by its maximal graded ideal), `n >= 1`, with
`c_{2,2n+1} = 1 - 3 (2n-1)^2 / (2n+1)`.  In the indexing of `twoSeriesLevels m` used below,
`n = m + 1`, so `m = 0` is the trivial endpoint `M(2,3)` (`c = 0`, `L = ℂ`) and `m = 1` is
Lee–Yang `M(2,5)`.

Main results (all `m : ℕ`, no further hypotheses):

* `classicallyFree`: the canonical differential-algebra map
  `J_∞(ℂ[T]/(T^{m+1})) → gr^{Li} L`, `T_{(j)} ↦` the divided `j`-th translate of the class
  of `ω`, is bijective (`LiPresentationClassicallyFree`).
* `baseC2AlgEquiv`: `ℂ[T]/(T^{m+1}) ≃ₐ A₂(L) = L / C₂(L)`, the full nonreduced `C₂` algebra.
* `actualC2ArcEquiv`: the presented jet algebra represents arcs of the actual `C₂` algebra.

Ingredients: the Virasoro word description of Li's filtration (`VirasoroWordLi`), the generic
generator-word surjectivity (`GeneratorWordLiSurjectivity`), the jet relations of the singular
vector and the leading-symbol theorem `virSymbol_twoSeries` (`TwoSeriesDSVirSymbol`).  This file
supplies the bridge from that PBW-length symbol theorem to the intrinsic Li statement.
-/

namespace VOA
namespace VirasoroClassicalFreeness

open VOA.VirModule VOA.VirSimple VOA.QuotVOA VOA.VirasoroLi
open scoped DirectSum

noncomputable section

variable (c : ℂ)

/-! ## §1  The simple quotient and its conformal generator -/

/-- The class of the conformal vector in the simple Virasoro VOA. -/
def omegaBar : VirUniv c ⧸ maxIdealVir c := (maxIdealVir c).mkQ (omegaVir c)

theorem omegaBar_mem : omegaBar c ∈ (virasoroSimple c).grading ((2 : ℕ) : ℤ) :=
  virasoroSimple_mkQ_grading c (omegaVir_mem_gradingVir_two c)

/-- One generator, the conformal vector, of weight two. -/
abbrev gen : Fin 1 → VirUniv c ⧸ maxIdealVir c := fun _ => omegaBar c

abbrev wt : Fin 1 → ℕ := fun _ => 2

theorem gen_mem : ∀ i, gen c i ∈ (virasoroSimple c).grading (wt i : ℤ) :=
  fun _ => omegaBar_mem c

/-- The degree-zero Li class of `ω`. -/
abbrev x : Fin 1 → liAssociatedGraded (virasoroSimple c) :=
  fun i => liDegreeZeroClass (virasoroSimple c) (wt i) ⟨gen c i, gen_mem c i⟩

theorem mkQ_negWordVir :
    ∀ w : List ℕ, (maxIdealVir c).mkQ (negWordVir c w) =
      genWordState (virasoroSimple c) (gen c) wt (virPairs w) := by
  intro w
  induction w with
  | nil => rfl
  | cons j rest ih =>
      change _ = wordAct (adjointWeakModule (virasoroSimple c))
          (genWord (gen c) wt (((0 : Fin 1), j) :: virPairs rest)) (virasoroSimple c).vacuum
      rw [negWordVir_cons_eq_smul, ← virasoroSimple_mkQ_smul, genWord_cons, wordAct_cons]
      change _ = (virasoroSimple c).smul (omegaBar c) (-(j : ℤ) - 1)
        (genWordState (virasoroSimple c) (gen c) wt (virPairs rest))
      rw [← ih]
      rfl

/-! ## §2  Word spanning and surjectivity -/

/-- Li's filtration of `L(c,0)` is spanned by Virasoro words of the right depth. -/
theorem genWordsSpan : GeneratorWordsSpanLiFiltration (virasoroSimple c) (gen c) wt := by
  intro p
  rw [simpleLiFiltration_eq_virWordPiece, virWordPiece, Submodule.map_span, Submodule.span_le]
  rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
  exact Submodule.subset_span ⟨virPairs w, by rw [pairsLevel_virPairs]; exact hw,
    (mkQ_negWordVir c w).symm⟩

theorem mkQ_negWordVir_mem_liFiltration (p : ℕ) (w : List ℕ) (hp : p ≤ virWordLevel w) :
    (maxIdealVir c).mkQ (negWordVir c w) ∈ liFiltration (virasoroSimple c) p := by
  rw [simpleLiFiltration_eq_virWordPiece]
  exact Submodule.mem_map_of_mem (negWordVir_mem_virWordPiece c p w hp)

/-! ## §3  The `C₂` relation `ω^{m+1} = 0` -/

theorem mk₂_mkQ_smul_neg_one (u v : VirUniv c) :
    mk₂ (virasoroSimple c) ((maxIdealVir c).mkQ ((virasoroVOA c).smul u (-1) v)) =
      mk₂ (virasoroSimple c) ((maxIdealVir c).mkQ u) *
        mk₂ (virasoroSimple c) ((maxIdealVir c).mkQ v) := by
  rw [← virasoroSimple_mkQ_smul]
  change _ = A₂mul (virasoroSimple c) _ _
  rw [A₂mul_mk, poissonMul_def]

theorem mk₂_replicate (k : ℕ) :
    mk₂ (virasoroSimple c) ((maxIdealVir c).mkQ (negWordVir c (List.replicate k 0))) =
      mk₂ (virasoroSimple c) (omegaBar c) ^ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [List.replicate_succ, negWordVir_cons_eq_smul, pow_succ', ← ih]
      exact mk₂_mkQ_smul_neg_one c _ _

theorem energyVir_eq (w : List ℕ) : energyVir w = virWordLevel w + 2 * w.length := by
  induction w with
  | nil => rfl
  | cons j rest ih =>
      simp only [energyVir, virWordLevel, List.sum_cons, List.length_cons] at ih ⊢
      omega

theorem virFil_le_virWordPiece_one (m : ℕ) :
    VirGoodFil.virFil c m ((2 * m + 2 + 0 : ℕ) : ℤ) ≤ virWordPiece c 1 := by
  rw [VirGoodFil.virFil, Submodule.span_le]
  rintro _ ⟨w, -, he, hl, rfl⟩
  apply negWordVir_mem_virWordPiece
  have he' : energyVir w = 2 * m + 2 := by exact_mod_cast he
  rw [energyVir_eq] at he'
  omega

/-- **The `C₂` relation.**  If the jet relations of the singular vector hold, then
`[ω]^{m+1} = 0` in the full nonreduced `C₂` algebra of `L(c,0)`. -/
theorem mk₂_omegaBar_pow_eq_zero (m : ℕ) (hJ : TwoSeriesCharacter.HasJetRelations c m) :
    mk₂ (virasoroSimple c) (omegaBar c) ^ (m + 1) = 0 := by
  obtain ⟨α, hα, h⟩ := hJ
  obtain ⟨σ, hσ, hrem⟩ := h 0
  rw [TwoSeriesCharacter.jetSum_zero_right] at hrem
  have hrem' := virFil_le_virWordPiece_one c m hrem
  have hO : (maxIdealVir c).mkQ (σ - α • negWordVir c (List.replicate (m + 1) 0)) ∈
      O₂ (virasoroSimple c) := by
    rw [← liFiltration_one_eq_O₂, simpleLiFiltration_eq_virWordPiece]
    exact Submodule.mem_map_of_mem hrem'
  have hσ0 : (maxIdealVir c).mkQ σ = 0 := (Submodule.Quotient.mk_eq_zero _).mpr hσ
  rw [map_sub, hσ0, zero_sub, map_smul] at hO
  have hO' : (maxIdealVir c).mkQ (negWordVir c (List.replicate (m + 1) 0)) ∈
      O₂ (virasoroSimple c) := by
    have := (O₂ (virasoroSimple c)).smul_mem (-α⁻¹) hO
    rwa [smul_neg, neg_smul, neg_neg, smul_smul, inv_mul_cancel₀ hα, one_smul] at this
  rw [← mk₂_replicate]
  exact (Submodule.Quotient.mk_eq_zero _).mpr hO'

/-- The relation ideal `(T^{m+1})` in one variable. -/
abbrev relIdeal (m : ℕ) : Ideal (MvPolynomial (Fin 1) ℂ) :=
  Ideal.span {MvPolynomial.X 0 ^ (m + 1)}

abbrev genGr : ∀ i, (virasoroSimple c).grading (wt i : ℤ) := fun i => ⟨gen c i, gen_mem c i⟩

theorem relIdeal_le_c2 (m : ℕ) (hJ : TwoSeriesCharacter.HasJetRelations c m) :
    relIdeal m ≤ RingHom.ker
      (MvPolynomial.aeval (fun i => mk₂ (virasoroSimple c) (genGr c i).1)).toRingHom := by
  rw [relIdeal, Ideal.span_le, Set.singleton_subset_iff]
  change MvPolynomial.aeval _ _ = 0
  rw [map_pow, MvPolynomial.aeval_X]
  exact mk₂_omegaBar_pow_eq_zero c m hJ

theorem relIdeal_le_li (m : ℕ) (hJ : TwoSeriesCharacter.HasJetRelations c m) :
    relIdeal m ≤ RingHom.ker (MvPolynomial.aeval (x c)).toRingHom :=
  liRelations_of_c2Relations (virasoroSimple c) wt (genGr c) (relIdeal m)
    (relIdeal_le_c2 c m hJ)

theorem jetMap_surjective (m : ℕ) (hJ : TwoSeriesCharacter.HasJetRelations c m) :
    Function.Surjective
      (liInfinitePresentedJetMap (virasoroSimple c) (x c) (relIdeal m) (relIdeal_le_li c m hJ)) :=
  liInfinitePresentedJetMap_surjective_of_genWordSpan (virasoroSimple c) (gen c) wt
    (gen_mem c) (genWordsSpan c) (relIdeal m) (relIdeal_le_li c m hJ)

/-! ## §4  Comparison of the presented jet algebra with `R_{m+1} = ℂ[T_j]/(jets of T^{m+1})` -/

abbrev JP := InfiniteJet.JetPoly ℂ (Fin 1)

/-- Forget the (unique) generator index of a jet variable. -/
def psi0 : JP →ₐ[ℂ] TwoSeries.StrictModel.TPoly :=
  MvPolynomial.aeval fun v => MvPolynomial.X v.2

/-- Reinsert the generator index. -/
def rho0 : TwoSeries.StrictModel.TPoly →ₐ[ℂ] JP :=
  MvPolynomial.aeval fun j => MvPolynomial.X ((0 : Fin 1), j)

theorem rho0_psi0 (h : JP) : rho0 (psi0 h) = h := by
  have hc : rho0.comp psi0 = AlgHom.id ℂ JP := by
    apply MvPolynomial.algHom_ext
    rintro ⟨i, j⟩
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    simp [psi0, rho0]
  exact DFunLike.congr_fun hc h

theorem map_rho0_tSer :
    PowerSeries.map (rho0 : TwoSeries.StrictModel.TPoly →+* JP) TwoSeries.StrictModel.tSer =
      InfiniteJet.generatorSeries (R := ℂ) (0 : Fin 1) := by
  ext j
  simp [TwoSeries.StrictModel.tSer, rho0, InfiniteJet.coeff_generatorSeries]

theorem rho0_coeff (n j : ℕ) :
    rho0 (PowerSeries.coeff j (TwoSeries.StrictModel.tSer ^ n)) =
      InfiniteJet.relationCoefficient (MvPolynomial.X (0 : Fin 1) ^ n : MvPolynomial (Fin 1) ℂ) j := by
  have ha : MvPolynomial.aeval (InfiniteJet.generatorSeries (R := ℂ) (σ := Fin 1))
      (MvPolynomial.X (0 : Fin 1) ^ n : MvPolynomial (Fin 1) ℂ) =
        InfiniteJet.generatorSeries (R := ℂ) (0 : Fin 1) ^ n := by
    simp
  rw [InfiniteJet.relationCoefficient, ha, ← map_rho0_tSer, ← map_pow, PowerSeries.coeff_map]
  rfl

theorem rho0_mem_jetIdeal (m : ℕ) {y : TwoSeries.StrictModel.TPoly}
    (hy : y ∈ TwoSeries.StrictModel.jetIdealT (m + 1)) :
    rho0 y ∈ InfiniteJet.jetIdeal (relIdeal m) := by
  have hmap : Ideal.map rho0 (TwoSeries.StrictModel.jetIdealT (m + 1)) ≤
      InfiniteJet.jetIdeal (relIdeal m) := by
    rw [TwoSeries.StrictModel.jetIdealT, Ideal.map_span, Ideal.span_le]
    rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
    rw [rho0_coeff]
    exact InfiniteJet.relationCoefficient_mem_jetIdeal _ _
      (Ideal.subset_span (Set.mem_singleton _)) j
  exact hmap (Ideal.mem_map_of_mem _ hy)

/-- The comparison map `J_∞ → R_{m+1}`, `T_{(j)} ↦ t_j`. -/
def psi (m : ℕ) : JP →ₐ[ℂ] TwoSeries.StrictModel.Rn (m + 1) :=
  (Ideal.Quotient.mkₐ ℂ _).comp psi0

theorem psi_X (m : ℕ) (v : Fin 1 × ℕ) :
    psi m (MvPolynomial.X v) = TwoSeries.StrictModel.tn (m + 1) v.2 := by
  simp [psi, psi0, TwoSeries.StrictModel.tn]

/-- **Presented-jet comparison.**  The kernel of `J_∞ → R_{m+1}` lies in the genuine jet ideal of
`(T^{m+1})`. -/
theorem mem_jetIdeal_of_psi_eq_zero (m : ℕ) (h : JP) (hh : psi m h = 0) :
    h ∈ InfiniteJet.jetIdeal (relIdeal m) := by
  have h1 : psi0 h ∈ TwoSeries.StrictModel.jetIdealT (m + 1) :=
    (Ideal.Quotient.eq_zero_iff_mem (I := TwoSeries.StrictModel.jetIdealT (m + 1))).mp
      (by simpa [psi] using hh)
  have h2 := rho0_mem_jetIdeal m h1
  rwa [rho0_psi0] at h2

/-! ## §5  Monomials as creation words -/

theorem prod_X_toList (d : Fin 1 × ℕ →₀ ℕ) :
    ((d.toMultiset.toList).map (fun v => (MvPolynomial.X v : JP))).prod =
      MvPolynomial.monomial d 1 := by
  rw [Multiset.prod_map_toList, Finsupp.toMultiset_apply, MvPolynomial.monomial_eq]
  simp only [Finsupp.sum, Finsupp.prod, map_one, one_mul]
  rw [← Multiset.coe_mapAddMonoidHom, map_sum]
  simp only [Multiset.coe_mapAddMonoidHom, Multiset.map_nsmul,
    Multiset.map_singleton, Multiset.prod_sum, Multiset.prod_nsmul,
    Multiset.prod_singleton]

theorem isWeightedHomogeneous_list_prod {M : Type*} [AddCommMonoid M] (w : Fin 1 × ℕ → M)
    (L : List (Fin 1 × ℕ)) :
    ((L.map (fun v => (MvPolynomial.X v : JP))).prod).IsWeightedHomogeneous w
      (L.map w).sum := by
  induction L with
  | nil => simpa using MvPolynomial.isWeightedHomogeneous_one (R := ℂ) w
  | cons v L ih =>
      simp only [List.map_cons, List.prod_cons, List.sum_cons]
      exact (MvPolynomial.isWeightedHomogeneous_X ℂ w v).mul ih

theorem weight_eq_toList_sum {M : Type*} [AddCommMonoid M] (w : Fin 1 × ℕ → M)
    (d : Fin 1 × ℕ →₀ ℕ) :
    Finsupp.weight w d = ((d.toMultiset.toList).map w).sum := by
  apply MvPolynomial.IsWeightedHomogeneous.inj_right (φ := (MvPolynomial.monomial d (1 : ℂ) : JP))
  · simp
  · exact MvPolynomial.isWeightedHomogeneous_monomial w d 1 rfl
  · rw [← prod_X_toList]
    exact isWeightedHomogeneous_list_prod w _

theorem sum_jetLiBidegree (L : List (Fin 1 × ℕ)) :
    (L.map (InfiniteJet.jetLiBidegree wt)).sum =
      (pairsLevel L, pairsLevel L + 2 * L.length) := by
  induction L with
  | nil => rfl
  | cons v L ih =>
      simp only [List.map_cons, List.sum_cons, ih, pairsLevel_cons, List.length_cons,
        InfiniteJet.jetLiBidegree, Prod.mk_add_mk, wt]
      ext <;> simp <;> omega

theorem wordDeg_genWord_wt (L : List (Fin 1 × ℕ)) (f : Fin 1 → VirUniv c ⧸ maxIdealVir c) :
    wordDeg (genWord f wt L) = pairsLevel L + 2 * L.length := by
  induction L with
  | nil => rfl
  | cons v L ih =>
      simp only [genWord_cons, wordDeg_cons, ih, pairsLevel_cons, List.length_cons, wt]
      omega

theorem virPairs_map_snd (L : List (Fin 1 × ℕ)) : virPairs (L.map Prod.snd) = L := by
  induction L with
  | nil => rfl
  | cons v L ih =>
      obtain ⟨i, n⟩ := v
      have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      simp only [List.map_cons, virPairs] at ih ⊢
      rw [ih]

theorem negWordVir_mem_grading_energy (w : List ℕ) :
    negWordVir c w ∈ (virasoroVOA c).grading (energyVir w : ℤ) := by
  have h := (generatorWord_mem_liWeightPiece (virasoroVOA c) (virGen c) (fun _ : Fin 1 => 2)
    (fun _ => omegaVir_mem_gradingVir_two c) (virPairs w)).2
  rw [← negWordVir_eq_generatorWord] at h
  have he : wordDeg (genWord (virGen c) (fun _ : Fin 1 => 2) (virPairs w)) = energyVir w := by
    induction w with
    | nil => rfl
    | cons j rest ih =>
        change wordDeg (genWord (virGen c) (fun _ : Fin 1 => 2)
          (((0 : Fin 1), j) :: virPairs rest)) = _
        rw [genWord_cons, wordDeg_cons, ih (by
          have := (generatorWord_mem_liWeightPiece (virasoroVOA c) (virGen c)
            (fun _ : Fin 1 => 2) (fun _ => omegaVir_mem_gradingVir_two c) (virPairs rest)).2
          rwa [← negWordVir_eq_generatorWord] at this)]
        simp only [energyVir]
        omega
  rwa [he] at h

/-- The polynomial-level infinite Li evaluation. -/
abbrev E : JP →ₐ[ℂ] liAssociatedGraded (virasoroSimple c) :=
  liInfiniteJetPolynomialMap (virasoroSimple c) (gen c) wt (gen_mem c)

theorem E_list_prod (L : List (Fin 1 × ℕ)) :
    E c ((L.map (fun v => (MvPolynomial.X v : JP))).prod) =
      liHomogeneousClass (virasoroSimple c) (pairsLevel L) (wordDeg (genWord (gen c) wt L))
        ⟨genWordState (virasoroSimple c) (gen c) wt L,
          generatorWord_mem_liWeightPiece _ (gen c) wt (gen_mem c) L⟩ := by
  rw [← prod_dividedIterate_degreeZeroClass_eq_generatorWord (virasoroSimple c) (gen c) wt
    (gen_mem c) L, map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro v _
  simp [liInfiniteJetPolynomialMap, InfiniteJet.derivationJetEval]

/-! ## §6  The key comparison lemma -/

theorem key (m : ℕ) (σ : VirUniv c →ₗ[ℂ] TwoSeries.StrictModel.Rn (m + 1)) (b : ℕ)
    (hσword : ∀ w : List ℕ, w.length = b →
      σ (negWordVir c w) = (w.map (TwoSeries.StrictModel.tn (m + 1))).prod)
    (p : ℕ) (h : JP)
    (hh : h.IsWeightedHomogeneous (InfiniteJet.jetLiBidegree wt) (p, p + 2 * b)) :
    ∃ v : VirUniv c, ∃ hv : (maxIdealVir c).mkQ v ∈
        liWeightPiece (virasoroSimple c) p (p + 2 * b),
      v ∈ (virasoroVOA c).grading ((p + 2 * b : ℕ) : ℤ) ∧
      E c h = liHomogeneousClass (virasoroSimple c) p (p + 2 * b) ⟨_, hv⟩ ∧
      psi m h = σ v := by
  induction hh using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero =>
      refine ⟨0, by rw [map_zero]; exact Submodule.zero_mem _, Submodule.zero_mem _, ?_, ?_⟩
      · rw [map_zero]
        have h0 : (⟨(maxIdealVir c).mkQ 0, by rw [map_zero]; exact Submodule.zero_mem _⟩ :
            liWeightPiece (virasoroSimple c) p (p + 2 * b)) = 0 :=
          Subtype.ext (map_zero _)
        rw [h0, liHomogeneousClass_zero]
      · simp
  | add f g hf hg ihf ihg =>
      obtain ⟨v₁, hv₁, hg₁, hE₁, hψ₁⟩ := ihf
      obtain ⟨v₂, hv₂, hg₂, hE₂, hψ₂⟩ := ihg
      refine ⟨v₁ + v₂, by rw [map_add]; exact Submodule.add_mem _ hv₁ hv₂,
        Submodule.add_mem _ hg₁ hg₂, ?_, by rw [map_add, map_add, hψ₁, hψ₂]⟩
      change E c (f + g) = _
      rw [map_add, hE₁, hE₂, ← liHomogeneousClass_add]
      congr 1
  | monomial d r hr =>
      set L := d.toMultiset.toList with hL
      have hwt := weight_eq_toList_sum (InfiniteJet.jetLiBidegree wt) d
      rw [hr, ← hL, sum_jetLiBidegree] at hwt
      have hp : pairsLevel L = p := (congrArg Prod.fst hwt).symm
      have hlen : L.length = b := by
        have := congrArg Prod.snd hwt
        simp only at this
        omega
      set w := L.map Prod.snd with hw
      have hwlen : w.length = b := by rw [hw, List.length_map, hlen]
      have hstate : (maxIdealVir c).mkQ (negWordVir c w) =
          genWordState (virasoroSimple c) (gen c) wt L := by
        rw [mkQ_negWordVir, hw, virPairs_map_snd]
      have hdeg : wordDeg (genWord (gen c) wt L) = p + 2 * b := by
        rw [wordDeg_genWord_wt, hp, hlen]
      have hpiece : genWordState (virasoroSimple c) (gen c) wt L ∈
          liWeightPiece (virasoroSimple c) p (p + 2 * b) := by
        have := generatorWord_mem_liWeightPiece _ (gen c) wt (gen_mem c) L
        rwa [hp, hdeg] at this
      have hmon : (MvPolynomial.monomial d r : JP) = r • (L.map (fun v => (MvPolynomial.X v : JP))).prod := by
        rw [hL, prod_X_toList, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
      refine ⟨r • negWordVir c w, ?_, ?_, ?_, ?_⟩
      · rw [map_smul, hstate]
        exact Submodule.smul_mem _ r hpiece
      · apply Submodule.smul_mem
        have := negWordVir_mem_grading_energy c w
        have he : energyVir w = p + 2 * b := by
          rw [energyVir_eq, hwlen, ← hp]
          rfl
        rwa [he] at this
      · rw [hmon, map_smul, E_list_prod]
        rw [liHomogeneousClass_reindex (virasoroSimple c) hp hdeg _ hpiece,
          ← liHomogeneousClass_smul]
        congr 1
        apply Subtype.ext
        change r • genWordState (virasoroSimple c) (gen c) wt L = (maxIdealVir c).mkQ (r • _)
        rw [map_smul, hstate]
      · rw [hmon, map_smul, map_smul, hσword w hwlen, map_list_prod, List.map_map, hw,
          List.map_map]
        congr 2
        apply List.map_congr_left
        intro v _
        simp [psi_X]

theorem eq_zero_of_odd (p N : ℕ) (hN : ¬ ∃ b, N = p + 2 * b) (h : JP)
    (hh : h.IsWeightedHomogeneous (InfiniteJet.jetLiBidegree wt) (p, N)) : h = 0 := by
  induction hh using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero => rfl
  | add f g hf hg ihf ihg => rw [ihf, ihg, add_zero]
  | monomial d r hr =>
      exfalso
      have hwt := weight_eq_toList_sum (InfiniteJet.jetLiBidegree wt) d
      rw [hr, sum_jetLiBidegree] at hwt
      apply hN
      refine ⟨(d.toMultiset.toList).length, ?_⟩
      have h1 := congrArg Prod.fst hwt
      have h2 := congrArg Prod.snd hwt
      simp only at h1 h2
      omega

/-! ## §7  Weight projection and injectivity -/

/-- The weight-`N` projection on the universal Virasoro VOA. -/
abbrev P (N : ℕ) : Module.End ℂ (VirUniv c) := wProj (adjointModule (virasoroVOA c)) (N : ℂ)

theorem P_of_mem {N : ℕ} {v : VirUniv c} (hv : v ∈ (virasoroVOA c).grading (N : ℤ)) :
    P c N v = v := by
  apply wProj_of_mem
  change v ∈ adjWeight (virasoroVOA c) (N : ℂ)
  have hcast : (N : ℂ) = ((N : ℤ) : ℂ) := by norm_num
  rw [hcast, adjWeight_cast]
  exact hv

theorem P_of_mem_ne {N : ℕ} {n : ℤ} {v : VirUniv c} (hv : v ∈ (virasoroVOA c).grading n)
    (hne : (N : ℤ) ≠ n) : P c N v = 0 := by
  apply wProj_of_mem_ne (β := (n : ℂ))
  · change v ∈ adjWeight (virasoroVOA c) (n : ℂ)
    rw [adjWeight_cast]
    exact hv
  · intro h
    apply hne
    exact_mod_cast h

/-- The maximal ideal is stable under weight projection (it is a graded ideal). -/
theorem P_mem_maxIdealVir (N : ℕ) {v : VirUniv c} (hv : v ∈ maxIdealVir c) :
    P c N v ∈ maxIdealVir c := by
  have hv' : v ∈ ⨆ n : ℤ, maxIdealVir c ⊓ (virasoroVOA c).grading n := by
    rw [← maxIdealVir_isGradedIdeal c]
    exact hv
  refine Submodule.iSup_induction _ (motive := fun z => P c N z ∈ maxIdealVir c) hv' ?_ ?_ ?_
  · intro n y hy
    show P c N y ∈ maxIdealVir c
    by_cases hn : (N : ℤ) = n
    · subst hn
      rw [P_of_mem c hy.2]
      exact hy.1
    · rw [P_of_mem_ne c hy.2 hn]
      exact Submodule.zero_mem _
  · show P c N 0 ∈ maxIdealVir c
    rw [map_zero]; exact Submodule.zero_mem _
  · intro x y hx hy
    show P c N (x + y) ∈ maxIdealVir c
    rw [map_add]; exact Submodule.add_mem _ hx hy

/-- Projecting a deeper word piece to weight `p + 2b` leaves only words of length `< b`. -/
theorem P_virWordPiece_mem_vBelow (p b : ℕ) {y : VirUniv c} (hy : y ∈ virWordPiece c (p + 1)) :
    P c (p + 2 * b) y ∈ TwoSeries.DSSlice.vBelow c b := by
  rw [virWordPiece] at hy
  induction hy using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨w, hw, rfl⟩ := hz
      have hg := negWordVir_mem_grading_energy c w
      by_cases he : energyVir w = p + 2 * b
      · rw [he] at hg
        rw [P_of_mem c hg]
        apply TwoSeries.DSSlice.negWordVir_mem_vBelow
        rw [energyVir_eq] at he
        omega
      · rw [P_of_mem_ne c hg (by exact_mod_cast (Ne.symm he))]
        exact Submodule.zero_mem _
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ a hx

/-- **Symbol vanishing.**  A homogeneous jet polynomial killed by the canonical map is killed by
the comparison map to `R_{m+1}`. -/
theorem psi_eq_zero_of_E_eq_zero (m : ℕ)
    (hsym : TwoSeries.DSSlice.VirSymbol c (TwoSeries.StrictModel.Rn (m + 1))
      (TwoSeries.StrictModel.tn (m + 1)))
    (p b : ℕ) (h : JP)
    (hh : h.IsWeightedHomogeneous (InfiniteJet.jetLiBidegree wt) (p, p + 2 * b))
    (hE : E c h = 0) : psi m h = 0 := by
  obtain ⟨σ, hmax, hbelow, hword⟩ := hsym
  obtain ⟨v, hv, hvgr, hEv, hψ⟩ :=
    key c m (σ b) b (fun w hw => by rw [← hw]; exact hword w) p h hh
  rw [hψ]
  have hz : liHomogeneousClass (virasoroSimple c) p (p + 2 * b) ⟨_, hv⟩ = 0 := hEv ▸ hE
  have hmem : (maxIdealVir c).mkQ v ∈ liFiltration (virasoroSimple c) (p + 1) := by
    have hi := DirectSum.of_injective
      (β := fun d : ℕ × ℕ => liWeightLayer (virasoroSimple c) d.1 d.2) (p, p + 2 * b)
    have hq := hi (hz.trans (map_zero _).symm)
    exact ((Submodule.Quotient.mk_eq_zero _).mp hq).1
  rw [simpleLiFiltration_eq_virWordPiece] at hmem
  obtain ⟨y, hy, hyv⟩ := Submodule.mem_map.mp hmem
  have hdiff : v - y ∈ maxIdealVir c :=
    (Submodule.Quotient.eq (maxIdealVir c)).mp hyv.symm
  have hsplit : v = P c (p + 2 * b) (v - y) + P c (p + 2 * b) y := by
    rw [map_sub, P_of_mem c hvgr]
    abel
  rw [hsplit, map_add, hmax b _ (P_mem_maxIdealVir c _ hdiff),
    hbelow b _ (P_virWordPiece_mem_vBelow c p b hy), add_zero]

/-- **Injectivity** of the canonical map, from the leading-symbol theorem. -/
theorem jetMap_injective (m : ℕ) (hJ : TwoSeriesCharacter.HasJetRelations c m)
    (hsym : TwoSeries.DSSlice.VirSymbol c (TwoSeries.StrictModel.Rn (m + 1))
      (TwoSeries.StrictModel.tn (m + 1))) :
    Function.Injective
      (liInfinitePresentedJetMap (virasoroSimple c) (x c) (relIdeal m) (relIdeal_le_li c m hJ)) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro y
  refine Submodule.Quotient.induction_on _ y fun f hf => ?_
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  have hf' : E c f = 0 := hf
  rw [← MvPolynomial.sum_weightedHomogeneousComponent (w := InfiniteJet.jetLiBidegree wt) f]
  apply QuotVOA.finsum_mem_submodule ((InfiniteJet.jetIdeal (relIdeal m)).restrictScalars ℂ)
  rintro ⟨p, N⟩
  have hcomp := liInfiniteJetPolynomialMap_weightedHomogeneousComponent_eq_zero_of_eq_zero
    (virasoroSimple c) (gen c) wt (gen_mem c) f hf' (p, N)
  have hhom := MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous
    (w := InfiniteJet.jetLiBidegree wt) (n := (p, N)) (φ := f)
  by_cases hb : ∃ b, N = p + 2 * b
  · obtain ⟨b, rfl⟩ := hb
    exact mem_jetIdeal_of_psi_eq_zero m _
      (psi_eq_zero_of_E_eq_zero c m hsym p b _ hhom hcomp)
  · rw [eq_zero_of_odd p N hb _ hhom]
    exact Submodule.zero_mem _

/-! ## §8  The `C₂` algebra is generated by `[ω]` -/

theorem aeval_c2_surjective :
    Function.Surjective (MvPolynomial.aeval (fun i => mk₂ (virasoroSimple c) (genGr c i).1) :
      MvPolynomial (Fin 1) ℂ →ₐ[ℂ] A₂ (virasoroSimple c)) := by
  intro z
  obtain ⟨u, rfl⟩ := mk₂_surjective _ z
  obtain ⟨v, rfl⟩ := (maxIdealVir c).mkQ_surjective u
  let F : MvPolynomial (Fin 1) ℂ →ₗ[ℂ] A₂ (virasoroSimple c) :=
    (MvPolynomial.aeval (fun i => mk₂ (virasoroSimple c) (genGr c i).1)).toLinearMap
  suffices hs : mk₂ (virasoroSimple c) ((maxIdealVir c).mkQ v) ∈ LinearMap.range F by
    obtain ⟨f, hf⟩ := hs
    exact ⟨f, hf⟩
  have hv : v ∈ Submodule.span ℂ (Set.range (negWordVir c)) := by
    rw [← negSpanVir, negSpanVir_eq_top c]
    exact Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨w, rfl⟩ := hz
      by_cases hsum : w.sum = 0
      · have hrep : w = List.replicate w.length 0 :=
          List.eq_replicate_iff.mpr ⟨rfl, fun a ha => List.sum_eq_zero_iff.mp hsum a ha⟩
        refine ⟨MvPolynomial.X 0 ^ w.length, ?_⟩
        change MvPolynomial.aeval _ _ = _
        rw [map_pow, MvPolynomial.aeval_X, hrep, mk₂_replicate, List.length_replicate]
      · have hO := mkQ_negWordVir_mem_liFiltration c 1 w (Nat.pos_of_ne_zero hsum)
        rw [liFiltration_one_eq_O₂] at hO
        refine ⟨0, ?_⟩
        rw [map_zero]
        exact ((Submodule.Quotient.mk_eq_zero _).mpr hO).symm
  | zero => rw [map_zero, map_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [map_add, map_add]; exact Submodule.add_mem _ ha hb
  | smul r a _ ha => rw [map_smul, map_smul]; exact Submodule.smul_mem _ r ha

/-- The canonical map intertwines the jet translation with the translation of `gr^{Li}`. -/
theorem jetMap_translation (m : ℕ) (hJ : TwoSeriesCharacter.HasJetRelations c m)
    (a : InfiniteJet.PresentedJet (relIdeal m)) :
    liInfinitePresentedJetMap (virasoroSimple c) (x c) (relIdeal m) (relIdeal_le_li c m hJ)
        (InfiniteJet.translation (relIdeal m) a) =
      liAssociatedGradedTranslation (virasoroSimple c)
        (liInfinitePresentedJetMap (virasoroSimple c) (x c) (relIdeal m)
          (relIdeal_le_li c m hJ) a) :=
  InfiniteJet.presentedJetToDifferentialAlgebra_translation _ _ _ _ _ _ a

/-! ## §9  The minimal models `M(2, 2m+3)`: unconditional statements -/

/-- The central charge of `M(2, 2m+3)`: `c = 13 - 3q - 12/q` with `q = 2m+3`, equivalently
`1 - 3(q-2)^2/q`. -/
abbrev cm (m : ℕ) : ℂ := (TwoSeries.twoSeriesLevels m).c

theorem cm_eq (m : ℕ) :
    cm m = 1 - 3 * (2 * (m : ℂ) + 1) ^ 2 / (2 * (m : ℂ) + 3) := by
  rw [cm, TwoSeries.twoSeriesLevels_c_eq_bsaCharge, VirModule.bsaCharge]
  have h : (2 * (m : ℂ) + 3) ≠ 0 := by
    have : (0 : ℝ) < 2 * (m : ℝ) + 3 := by positivity
    intro h0
    have := congrArg Complex.re h0
    simp at this
    linarith
  have h' : (((2 * m + 2 : ℕ) : ℂ) + 1) = 2 * (m : ℂ) + 3 := by push_cast; ring
  rw [h']
  field_simp
  ring

theorem hasJetRelations (m : ℕ) : TwoSeriesCharacter.HasJetRelations (cm m) m :=
  TwoSeries.twoSeries_hasJetRelations_all m

/-- The relations `T^{m+1}` hold in `gr^{Li}` of `M(2,2m+3)`. -/
theorem relIdeal_le (m : ℕ) :
    relIdeal m ≤ RingHom.ker (MvPolynomial.aeval (x (cm m))).toRingHom :=
  relIdeal_le_li (cm m) m (hasJetRelations m)

/-- **Classical freeness of `M(2, 2m+3)`, for every `m : ℕ`.**  The canonical map
`J_∞(ℂ[T]/(T^{m+1})) → gr^{Li} L(c_{2,2m+3}, 0)` is bijective.  `m = 0` is the trivial endpoint
`M(2,3)` (`c = 0`); `m = 1` is Lee–Yang `M(2,5)`. -/
theorem classicallyFree (m : ℕ) :
    LiPresentationClassicallyFree (virasoroSimple (cm m)) (x (cm m)) (relIdeal m)
      (relIdeal_le m) :=
  ⟨jetMap_injective (cm m) m (hasJetRelations m) (TwoSeries.DSSlice.virSymbol_twoSeries m),
    jetMap_surjective (cm m) m (hasJetRelations m)⟩

/-- The canonical isomorphism `J_∞(ℂ[T]/(T^{m+1})) ≃ gr^{Li} L(c_{2,2m+3}, 0)`. -/
def canonicalEquiv (m : ℕ) :
    InfiniteJet.PresentedJet (relIdeal m) ≃ₐ[ℂ] liAssociatedGraded (virasoroSimple (cm m)) :=
  AlgEquiv.ofBijective _ (classicallyFree m)

/-- **The full nonreduced `C₂` algebra of `M(2, 2m+3)`** is `ℂ[T]/(T^{m+1})`, `T ↦ [ω]`. -/
def baseC2AlgEquiv (m : ℕ) :
    (MvPolynomial (Fin 1) ℂ ⧸ relIdeal m) ≃ₐ[ℂ] A₂ (virasoroSimple (cm m)) :=
  baseC2AlgEquiv_of_arc_injective (virasoroSimple (cm m)) wt (genGr (cm m)) (relIdeal m)
    (relIdeal_le_c2 (cm m) m (hasJetRelations m)) (relIdeal_le m) (classicallyFree m).1
    (aeval_c2_surjective (cm m))

/-- The presented jet algebra represents arcs of the actual `C₂` algebra: this bijection is natural
in the coefficient algebra (`actualC2ArcEquiv_natural`), so the presented jet algebra is
`J_∞(A₂(L))`. -/
def actualC2ArcEquiv (m : ℕ) {A : Type*} [CommRing A] [Algebra ℂ A] :
    (InfiniteJet.PresentedJet (relIdeal m) →ₐ[ℂ] A) ≃
      (A₂ (virasoroSimple (cm m)) →ₐ[ℂ] PowerSeries A) :=
  InfiniteJet.arcEquivOfBaseAlgebraEquiv (relIdeal m) (baseC2AlgEquiv m)

/-- Naturality of `actualC2ArcEquiv` in the coefficient algebra. -/
theorem actualC2ArcEquiv_natural (m : ℕ) {A B : Type*} [CommRing A] [Algebra ℂ A]
    [CommRing B] [Algebra ℂ B] (f : InfiniteJet.PresentedJet (relIdeal m) →ₐ[ℂ] A)
    (g : A →ₐ[ℂ] B) :
    actualC2ArcEquiv m (g.comp f) = (PowerSeries.mapAlgHom g).comp (actualC2ArcEquiv m f) :=
  InfiniteJet.arcEquivOfBaseAlgebraEquiv_natural _ _ f g

/-! ## §10  Named endpoints -/

/-- The trivial endpoint `M(2,3)`: `m = 0`, central charge `0`. -/
theorem cm_zero : cm 0 = 0 := by
  rw [cm_eq]; norm_num

/-- Lee–Yang `M(2,5)`: `m = 1`, central charge `-22/5`. -/
theorem cm_one : cm 1 = -22 / 5 := by
  rw [cm_eq]; norm_num

/-- Classical freeness at the trivial endpoint `M(2,3)` (`c = 0`, `R = ℂ[T]/(T)`). -/
theorem classicallyFree_M23 :
    LiPresentationClassicallyFree (virasoroSimple (cm 0)) (x (cm 0)) (relIdeal 0)
      (relIdeal_le 0) :=
  classicallyFree 0

/-- Classical freeness of Lee–Yang `M(2,5)` (`c = -22/5`, `R = ℂ[T]/(T²)`). -/
theorem classicallyFree_leeYang :
    LiPresentationClassicallyFree (virasoroSimple (cm 1)) (x (cm 1)) (relIdeal 1)
      (relIdeal_le 1) :=
  classicallyFree 1

end

end VirasoroClassicalFreeness
end VOA
