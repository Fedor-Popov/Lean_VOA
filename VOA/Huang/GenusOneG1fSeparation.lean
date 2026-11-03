import VOA.Huang.GenusOneG1fSepBraid
import VOA.Huang.VerlindeRhoReduction
import VOA.Modules.ZhuVermaAnArchDLM3PBWAxiom

/-!
# `TraceSeparationInput` — and Huang's Theorem 5.2

`TraceSeparation F hv c η'` (`GenusOneG1eIndependence`, the algebraic core of Huang 2008,
Prop. 2.11): if, for every insertion and every `n ∈ κ − 1 + ℤ`, a combination of the vacuum
traces `Σ_z coef_z Z_z(Y^ε[w_a]_n w_b)` equals a combination of traces of bracket modes of
`(a,b)`- and `(b,a)`-orthogonal channels of integral inner weight, then `coef = 0`.

Proof (`traceSeparationInput_holds`). Fix `v ∈ V_[k]`.
1. *Spanning.* `η'(v) = Σ_s c_s 𝒴[C w_s]_{n_s} C x_s` with `𝒴` the universal intertwiner of
   `M_a ⊠ M_b` (`coeff_mem_of_bracket` + `modeSpan_eq_top`); every term is realized by an
   insertion (`exists_insertion`).
2. *Weight extraction.* For every module map `g` out of `M_a ⊠ M_b` into a lowest-weight module,
   `g ∘ 𝒴[·]` is a bracket field, `L[0]`-homogeneous of weight `κ_s − n_s − 1`
   (`bracketModes_weight`); keeping the terms of weight `k` (`eigen_extract`):
   `ε(Σ' c_s X_s) = v`, `q(Σ' c_s X_s) = 0` for every `q` with `η' ≫ q = 0`, and
   `(R' ≫ q)(Σ' c_s X_s) = 0` for every `q` with `η ≫ q = 0` (`R' η' ∝ η`, `vacuum_hom_unique`).
3. *Traces.* Summing the hypothesis over the kept terms: the vacuum side is `Σ_z coef_z Z_z(v)`;
   every `(a,b)` channel gives `Tr(q(Σ' c_s X_s)) = 0`; every `(b,a)` channel gives, by the
   trace-level bracket skew-symmetry and the braiding (`postcompose_ba_eq_skew`), the constant
   phase `e^{iπκ_s} e^{iπ(−n_s−1)} = e^{iπk}` times `Tr((R' ≫ q)(Σ' c_s X_s)) = 0`.
4. Zhu's trace independence (`traceIndependent_of_irredundant`, PBW) gives `coef = 0`.

Headline: `fusionEigenInput_holds : VerlindeEigen.FusionEigenInput` (Huang's Theorem 5.2).
-/

noncomputable section

namespace VOA.Huang.GenusOneG1f

open VOA VOA.Huang Complex CategoryTheory
open VOA.Classification.COne VOA.Huang.VerlindeFusion VOA.Huang.TensorCat
  VOA.Huang.VerlindeTransport VOA.Huang.FusionUnit VOA.Huang.GenusOneG1d
open VOA.Huang.GenusOne (sqL traceFunction)
open VOA.Huang.GenusOne.IntCoord (bracketModes)
open VOA.Huang.GenusTwoPoint (vacuumLW)
open VOA.Huang.GenusTwoPoint.Separate (normalizedCoordinateChange
  normalizedModuleZeroConjugation_holds)
open VOA.Huang.FusionProduct (postcompose)
open VOA.Huang.GenusOneG1c (epsInt)
open scoped BigOperators

universe u w

variable {𝒱 : Type u} [AddCommGroup 𝒱] [Module ℂ 𝒱] {W : VertexOperatorAlgebra 𝒱}

/-! ## §1 Helpers -/

/-- Every vector of a lowest-weight module is a finite sum of ordinary-homogeneous vectors on
the lowest-weight coset. -/
theorem exists_weight_family (P : LWModule W) (u : P.carrier) :
    ∃ (m : ℕ) (ws : Fin m → P.carrier) (αs : Fin m → ℂ),
      (∀ i, ws i ∈ P.isMod.weight (αs i)) ∧ (∀ i, ∃ k : ℕ, αs i = P.h + k) ∧
        ∑ i, ws i = u := by
  refine FusionTop.induction_weight P.isMod u ?_ ?_ ?_
  · exact ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, by simp⟩
  · rintro x y ⟨m₁, w₁, α₁, h₁, l₁, s₁⟩ ⟨m₂, w₂, α₂, h₂, l₂, s₂⟩
    refine ⟨m₁ + m₂, Fin.append w₁ w₂, Fin.append α₁ α₂, ?_, ?_, ?_⟩
    · intro i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · simpa using h₁ i
      · simpa using h₂ i
    · intro i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · simpa using l₁ i
      · simpa using l₂ i
    · rw [Fin.sum_univ_add]
      simp [s₁, s₂]
  · intro α x hx
    rcases FusionTop.eq_zero_or_level P hx with rfl | ⟨k, rfl⟩
    · exact ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, by simp⟩
    · exact ⟨1, fun _ => x, fun _ => P.h + k, fun _ => hx, fun _ => ⟨k, rfl⟩, by simp⟩

variable {ι : Type w} [Fintype ι] [DecidableEq ι]

/-- An insertion realizing the coordinate-changed pair `(C w, C x)`. -/
theorem exists_insertion (D : VOA.ModularData W ι) (a b : ι) {α β : ℂ}
    {w : (lwOf D a).carrier} {x : (lwOf D b).carrier} (hw : w ∈ (lwOf D a).isMod.weight α)
    (hx : x ∈ (lwOf D b).isMod.weight β) :
    ∃ ins : Insertion D a b, (∑ i, ins.wa i) = normalizedCoordinateChange (lwOf D a) w ∧
      (∑ j, ins.wb j) = normalizedCoordinateChange (lwOf D b) x ∧ ins.κ = α + β := by
  obtain ⟨m, wa, αa, hwa, -, hsa⟩ := exists_weight_family (lwOf D a)
    (normalizedCoordinateChange (lwOf D a) w)
  obtain ⟨n, wb, αb, hwb, hlb, hsb⟩ := exists_weight_family (lwOf D b)
    (normalizedCoordinateChange (lwOf D b) x)
  refine ⟨⟨m, n, wa, αa, hwa, wb, αb, hwb, hlb, α, β, ?_, ?_⟩, hsa, hsb, rfl⟩
  · rw [hsa, normalizedModuleZeroConjugation_holds (lwOf D a) w,
      (lwOf D a).isMod.L0_weight α w hw, map_smul]
  · rw [hsb, normalizedModuleZeroConjugation_holds (lwOf D b) x,
      (lwOf D b).isMod.L0_weight β x hx, map_smul]

/-- Extraction of one eigencomponent from a finite sum of eigenvectors. -/
theorem eigen_extract {E : Type*} [AddCommGroup E] [Module ℂ E] (T : Module.End ℂ E)
    {κ : Type*} (s : Finset κ) (c : κ → ℂ) (y : κ → E) (k : κ → ℂ)
    (hy : ∀ i, T (y i) = k i • y i) (k0 : ℂ) (z : E) (hz : T z = k0 • z)
    (hsum : ∑ i ∈ s, c i • y i = z) :
    ∑ i ∈ s.filter (fun i => k i = k0), c i • y i = z := by
  classical
  set Dz := ∑ i ∈ s.filter (fun i => ¬ k i = k0), c i • y i with hDz
  have hsplit : z = ∑ i ∈ s.filter (fun i => k i = k0), c i • y i + Dz := by
    rw [← hsum, hDz, Finset.sum_filter_add_sum_filter_not]
  have h1 : Dz ∈ Module.End.eigenspace T k0 := by
    have : Dz = z - ∑ i ∈ s.filter (fun i => k i = k0), c i • y i := by
      rw [hsplit]; abel
    rw [this]
    refine Submodule.sub_mem _ (Module.End.mem_eigenspace_iff.mpr hz) ?_
    refine Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ ?_
    have hk : k i = k0 := (Finset.mem_filter.mp hi).2
    exact Module.End.mem_eigenspace_iff.mpr (by rw [hy i, hk])
  have h2 : Dz ∈ ⨆ μ ∈ {μ : ℂ | μ ≠ k0}, Module.End.eigenspace T μ := by
    refine Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ ?_
    have hk : k i ≠ k0 := (Finset.mem_filter.mp hi).2
    exact Submodule.mem_iSup_of_mem (k i) (Submodule.mem_iSup_of_mem hk
      (Module.End.mem_eigenspace_iff.mpr (hy i)))
  have hdis : Disjoint (Module.End.eigenspace T k0)
      (⨆ μ ∈ {μ : ℂ | μ ≠ k0}, Module.End.eigenspace T μ) :=
    (Module.End.eigenspaces_iSupIndep T).disjoint_biSup (by simp)
  have h0 : Dz = 0 := Submodule.disjoint_def.mp hdis _ h1 h2
  rw [hsplit, h0, add_zero]

theorem sum_linear {E : Type*} [AddCommGroup E] [Module ℂ E] (ℓ : E →ₗ[ℂ] ℂ) {κ : Type*}
    (s : Finset κ) (c : κ → ℂ) (y : κ → E) :
    ∑ i ∈ s, c i * ℓ (y i) = ℓ (∑ i ∈ s, c i • y i) := by
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_eq_mul]

/-! ## §2 The separation theorem -/

section Main

variable (F : FusionChoice W) (D : VOA.ModularData W ι) (a b : ι)

/-- The bracket coefficients of coordinate-changed homogeneous insertions. -/
def bracketSet : Set (tensorObj F (famObj D a) (famObj D b)).carrier :=
  {y | ∃ (n α β : ℂ) (w : (lwOf D a).carrier) (x : (lwOf D b).carrier),
    w ∈ (lwOf D a).isMod.weight α ∧ x ∈ (lwOf D b).isMod.weight β ∧
      y = bracketGen (P := lwOf D a) (Q := lwOf D b) (F (famObj D a) (famObj D b)).intertwiner n
        (normalizedCoordinateChange (lwOf D a) w) (normalizedCoordinateChange (lwOf D b) x)}

/-- **They span the fusion product.** -/
theorem bracketSet_span (y : (tensorObj F (famObj D a) (famObj D b)).carrier) :
    y ∈ Submodule.span ℂ (bracketSet F D a b) := by
  have hcoef := coeff_mem_of_bracket (P := lwOf D a) (Q := lwOf D b)
    (F (famObj D a) (famObj D b)).intertwiner (Submodule.span ℂ (bracketSet F D a b))
    (fun n α β w x hw hx => Submodule.subset_span ⟨n, α, β, w, x, hw, hx, rfl⟩)
  have hle : modeSpan (F (famObj D a) (famObj D b)) ≤ Submodule.span ℂ (bracketSet F D a b) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨n, x, y, rfl⟩
    exact hcoef n x y
  have htop := modeSpan_eq_top (F (famObj D a) (famObj D b))
  rw [htop] at hle
  exact hle Submodule.mem_top

end Main

section Final

open VOA.Huang.GenusOneG1e (genTerm genA genK TraceSeparation TraceSeparationInput)

variable (F : FusionChoice W) (D : VOA.ModularData W ι) (a b : ι)

/-- The universal bracket vector `𝒴[C w]_n C x ∈ M_a ⊠ M_b`. -/
def bvec (n : ℂ) (w : (lwOf D a).carrier) (x : (lwOf D b).carrier) :
    (tensorObj F (famObj D a) (famObj D b)).carrier :=
  bracketGen (P := lwOf D a) (Q := lwOf D b) (F (famObj D a) (famObj D b)).intertwiner n
    (normalizedCoordinateChange (lwOf D a) w) (normalizedCoordinateChange (lwOf D b) x)

/-- The kept indices: output `L[0]`-weight `k`. -/
def kept {m : ℕ} (αα ββ nn : Fin m → ℂ) (k : ℂ) : Finset (Fin m) :=
  Finset.univ.filter (fun i => αα i + ββ i - nn i - 1 = k)

theorem map_bvec (N : LWModule W)
    (g : homSpace (tensorObj F (famObj D a) (famObj D b)).isMod N.isMod) (n : ℂ)
    (w : (lwOf D a).carrier) (x : (lwOf D b).carrier) :
    g.val (bvec F D a b n w x) = bracketModes (postcompose (F (famObj D a) (famObj D b)).intertwiner
      N.isMod g) n (normalizedCoordinateChange (lwOf D a) w)
        (normalizedCoordinateChange (lwOf D b) x) :=
  map_bracketGen (P := lwOf D a) (Q := lwOf D b) _ N g n _ _

/-- **Weight extraction through a module map.** -/
theorem extract {m : ℕ} (cs nn αα ββ : Fin m → ℂ) (ww : Fin m → (lwOf D a).carrier)
    (xx : Fin m → (lwOf D b).carrier) (hww : ∀ i, ww i ∈ (lwOf D a).isMod.weight (αα i))
    (hxx : ∀ i, xx i ∈ (lwOf D b).isMod.weight (ββ i))
    (y : (tensorObj F (famObj D a) (famObj D b)).carrier)
    (hsum : ∑ i, cs i • bvec F D a b (nn i) (ww i) (xx i) = y) (k : ℂ) (N : LWModule W)
    (g : homSpace (tensorObj F (famObj D a) (famObj D b)).isMod N.isMod)
    (hz : sqL N.isMod 0 (g.val y) = k • g.val y) :
    ∑ i ∈ kept αα ββ nn k, cs i • g.val (bvec F D a b (nn i) (ww i) (xx i)) = g.val y := by
  refine eigen_extract (sqL N.isMod 0) Finset.univ cs
    (fun i => g.val (bvec F D a b (nn i) (ww i) (xx i))) (fun i => αα i + ββ i - nn i - 1) ?_ k
    _ hz ?_
  · intro i
    have hCw : sqL (lwOf D a).isMod 0 (normalizedCoordinateChange (lwOf D a) (ww i)) =
        αα i • normalizedCoordinateChange (lwOf D a) (ww i) := by
      rw [normalizedModuleZeroConjugation_holds (lwOf D a) (ww i),
        (lwOf D a).isMod.L0_weight _ _ (hww i), map_smul]
    have hCx : sqL (lwOf D b).isMod 0 (normalizedCoordinateChange (lwOf D b) (xx i)) =
        ββ i • normalizedCoordinateChange (lwOf D b) (xx i) := by
      rw [normalizedModuleZeroConjugation_holds (lwOf D b) (xx i),
        (lwOf D b).isMod.L0_weight _ _ (hxx i), map_smul]
    simp only
    rw [map_bvec]
    exact bracketModes_weight _ hCw hCx (nn i)
  · rw [← hsum, map_sum]
    exact Finset.sum_congr rfl fun i _ => (map_smul g.val (cs i) _).symm

/-- The `(a,b)`-channel coefficient through the universal bracket vector. -/
theorem genA_inl {η' : (vacuumObject : Ordinary W) ⟶ tensorObj F (famObj D a) (famObj D b)}
    {η : (vacuumObject : Ordinary W) ⟶ tensorObj F (famObj D b) (famObj D a)}
    (C : ABChannel F D a b η') (ins : Insertion D a b) (n : ℂ) (τ : UpperHalfPlane)
    (w : (lwOf D a).carrier) (x : (lwOf D b).carrier)
    (ha : (∑ i, ins.wa i) = normalizedCoordinateChange (lwOf D a) w)
    (hb : (∑ j, ins.wb j) = normalizedCoordinateChange (lwOf D b) x) :
    genA (Sum.inl C : VOA.Huang.GenusOneG1e.Gen F η' η) ins n τ =
      traceFunction C.Yout (D.h C.y) (C.q.val (bvec F D a b n w x)) τ := by
  change traceFunction C.Yout (D.h C.y) (bracketModes C.inner n (∑ j, ins.wa j)
    (∑ j, ins.wb j)) τ = _
  rw [ha, hb]
  exact congrArg (fun u => traceFunction C.Yout (D.h C.y) u τ)
    (map_bvec F D a b (lwOf D C.k) C.q n w x).symm

/-- The `(b,a)`-channel coefficient through the universal bracket vector (braiding + bracket
skew-symmetry at trace level). -/
theorem genA_inr (hC2 : C2Cofinite W)
    {η' : (vacuumObject : Ordinary W) ⟶ tensorObj F (famObj D a) (famObj D b)}
    {η : (vacuumObject : Ordinary W) ⟶ tensorObj F (famObj D b) (famObj D a)}
    (B : BAChannel F D a b η) (ins : Insertion D a b) (n : ℂ) (τ : UpperHalfPlane)
    (w : (lwOf D a).carrier) (x : (lwOf D b).carrier)
    (ha : (∑ i, ins.wa i) = normalizedCoordinateChange (lwOf D a) w)
    (hb : (∑ j, ins.wb j) = normalizedCoordinateChange (lwOf D b) x) :
    genA (Sum.inr B : VOA.Huang.GenusOneG1e.Gen F η' η) ins n τ =
      exp ((Real.pi : ℂ) * I * ins.κ) * (exp ((Real.pi : ℂ) * I * (-n - 1)) *
        traceFunction B.Yout (D.h B.y) ((braidR F D a b ≫ B.q).val (bvec F D a b n w x)) τ) := by
  change exp ((Real.pi : ℂ) * I * ins.κ) * traceFunction B.Yout (D.h B.y)
    (bracketModes B.inner n (∑ j, ins.wb j) (∑ j, ins.wa j)) τ = _
  rw [ha, hb]
  congr 1
  rw [traceFunction_bracketModes_skew hC2 (P := lwOf D a) (Q := lwOf D b)
    (N := lwOf D B.k) (R := lwOf D B.y) (lwOf_irreducible D B.k)
    (postcompose (F (famObj D a) (famObj D b)).intertwiner (lwOf D B.k).isMod
      (braidR F D a b ≫ B.q)) B.inner
    (postcompose_ba_eq_skew F D a b B.q) B.Yout (D.hasWeight B.y) n _ _ τ]
  congr 1
  exact congrArg (fun u => traceFunction B.Yout (D.h B.y) u τ)
    (map_bvec F D a b (lwOf D B.k) (braidR F D a b ≫ B.q) n w x).symm

/-- **The trace-separation statement (Huang 2008, Prop. 2.11 at trace level).** -/
theorem traceSeparation_holds (hNice : Nice W) (hirr : Irredundant D.Mfam)
    (c : TransferChoice F D a b) (hv : W.vacuum ≠ 0)
    (η' : (vacuumObject : Ordinary W) ⟶ tensorObj F (famObj D a) (famObj D b))
    (hη' : η' ≫ c.ε = 𝟙 _) : TraceSeparation F hv c η' := by
  classical
  intro coef r lam G hH
  have hC2 : C2Cofinite W := hNice.1.c2Cofinite
  refine VOA.Huang.VerlindeRho.traceIndependent_of_irredundant
    (VOA.VHat.DLM3.voaPBWBottomProjection _) D hC2 hirr coef ?_
  intro k v hvk τ
  obtain ⟨m, cs, gs, hgs⟩ := Submodule.mem_span_set'.mp (bracketSet_span F D a b (η'.val v))
  have hdata := fun i => (gs i).property
  choose nn αα ββ ww xx hww hxx hgseq using hdata
  choose ins hinsa hinsb hinsκ using fun i => exists_insertion D a b (hww i) (hxx i)
  have hsumX : ∑ i, cs i • bvec F D a b (nn i) (ww i) (xx i) = η'.val v := by
    rw [← hgs]
    exact Finset.sum_congr rfl fun i _ => by rw [hgseq i]; rfl
  have hext := extract F D a b cs nn αα ββ ww xx hww hxx (η'.val v) hsumX (k : ℂ)
  have hz0 : ∀ (N : LWModule W) (y : N.carrier), y = 0 → sqL N.isMod 0 y = (k : ℂ) • y := by
    intro N y hy
    subst hy
    rw [map_zero, smul_zero]
  -- the vacuum side
  have hεv : c.ε.val (η'.val v) = v := by
    have := congrArg (fun f : (vacuumObject : Ordinary W) ⟶ vacuumObject => f.val v) hη'
    simpa using this
  have hvw : sqL (vacuumLW W hv).isMod 0 v = (k : ℂ) • v := by
    change sqL (adjointModule W) 0 v = _
    rw [VOA.Huang.GenusOneG1e.sqL_adjoint_zero]
    exact (mem_sqWeightSpace_iff W _ v).mp hvk
  have hε : ∑ i ∈ kept αα ββ nn (k : ℂ), cs i • c.ε.val (bvec F D a b (nn i) (ww i) (xx i)) =
      v := by
    have h := hext (vacuumLW W hv) c.ε (by erw [hεv]; exact hvw)
    erw [hεv] at h
    exact h
  -- the (a,b) channels
  have hAB : ∀ C : ABChannel F D a b η',
      ∑ i ∈ kept αα ββ nn (k : ℂ), cs i • C.q.val (bvec F D a b (nn i) (ww i) (xx i)) = 0 := by
    intro C
    have hq0 : C.q.val (η'.val v) = 0 := by
      have := congrArg (fun f : (vacuumObject : Ordinary W) ⟶ famObj D C.k => f.val v) C.hq
      simpa using this
    have h := hext (lwOf D C.k) C.q (hz0 _ _ hq0)
    erw [hq0] at h
    exact h
  -- the (b,a) channels
  have hBA : ∀ B : BAChannel F D a b c.η,
      ∑ i ∈ kept αα ββ nn (k : ℂ),
        cs i • (braidR F D a b ≫ B.q).val (bvec F D a b (nn i) (ww i) (xx i)) = 0 := by
    intro B
    obtain ⟨μ, hμ⟩ := vacuum_hom_unique hNice F D a b hv c.η_ne (η' ≫ braidR F D a b)
    have hq0 : (braidR F D a b ≫ B.q).val (η'.val v) = 0 := by
      have h1 : (η' ≫ braidR F D a b ≫ B.q) = μ • (c.η ≫ B.q) := by
        rw [← Category.assoc, hμ, Linear.smul_comp]
      rw [B.hq, smul_zero] at h1
      have := congrArg (fun f : (vacuumObject : Ordinary W) ⟶ famObj D B.k => f.val v) h1
      simpa using this
    have h := hext (lwOf D B.k) (braidR F D a b ≫ B.q) (hz0 _ _ hq0)
    erw [hq0] at h
    exact h
  -- each generator contributes zero on the kept terms
  have hgen : ∀ g : VOA.Huang.GenusOneG1e.Gen F η' c.η,
      ∑ i ∈ kept αα ββ nn (k : ℂ), cs i * genTerm g (ins i) (nn i) τ = 0 := by
    intro g
    unfold genTerm
    split_ifs with hint
    · rcases g with C | B
      · simp only [fun i => genA_inl F D a b (η := c.η) C (ins i) (nn i) τ (ww i) (xx i)
          (hinsa i) (hinsb i)]
        refine (sum_linear (VOA.Huang.GenusOneG1e.tfLin hC2 (lwOf_irreducible D C.k) C.Yout
          (D.hasWeight C.y) τ) (kept αα ββ nn (k : ℂ)) cs
          (fun i => C.q.val (bvec F D a b (nn i) (ww i) (xx i)))).trans ?_
        exact (congrArg (VOA.Huang.GenusOneG1e.tfLin hC2 (lwOf_irreducible D C.k) C.Yout
          (D.hasWeight C.y) τ) (hAB C)).trans (map_zero _)
      · have hB : ∀ i ∈ kept αα ββ nn (k : ℂ),
            genA (Sum.inr B : VOA.Huang.GenusOneG1e.Gen F η' c.η) (ins i) (nn i) τ =
            exp ((Real.pi : ℂ) * I * k) * traceFunction B.Yout (D.h B.y)
              ((braidR F D a b ≫ B.q).val (bvec F D a b (nn i) (ww i) (xx i))) τ := by
          intro i hi
          have hki : αα i + ββ i - nn i - 1 = (k : ℂ) := (Finset.mem_filter.mp hi).2
          rw [genA_inr F D a b hC2 B (ins i) (nn i) τ (ww i) (xx i) (hinsa i) (hinsb i),
            ← mul_assoc, ← Complex.exp_add, hinsκ i]
          congr 2
          rw [← hki]
          ring
        rw [Finset.sum_congr rfl fun i hi => by rw [hB i hi]]
        have : ∀ i, cs i * (exp ((Real.pi : ℂ) * I * k) * traceFunction B.Yout (D.h B.y)
            ((braidR F D a b ≫ B.q).val (bvec F D a b (nn i) (ww i) (xx i))) τ) =
            exp ((Real.pi : ℂ) * I * k) * (cs i * traceFunction B.Yout (D.h B.y)
            ((braidR F D a b ≫ B.q).val (bvec F D a b (nn i) (ww i) (xx i))) τ) :=
          fun i => by ring
        simp only [this]
        rw [← Finset.mul_sum]
        have hs := (sum_linear (VOA.Huang.GenusOneG1e.tfLin hC2 (lwOf_irreducible D B.k) B.Yout
          (D.hasWeight B.y) τ) (kept αα ββ nn (k : ℂ)) cs
          (fun i => (braidR F D a b ≫ B.q).val (bvec F D a b (nn i) (ww i) (xx i))))
        have hs' := hs.trans ((congrArg (VOA.Huang.GenusOneG1e.tfLin hC2 (lwOf_irreducible D B.k)
          B.Yout (D.hasWeight B.y) τ) (hBA B)).trans (map_zero _))
        exact (congrArg (fun t => exp ((Real.pi : ℂ) * I * k) * t) hs').trans (mul_zero _)
    · simp
  -- the hypothesis on the kept terms
  have hHi : ∀ i ∈ kept αα ββ nn (k : ℂ),
      ∑ z, coef z * traceFun D.Mfam D.h z (c.ε.val (bvec F D a b (nn i) (ww i) (xx i))) τ =
        ∑ l, lam l * genTerm (G l) (ins i) (nn i) τ := by
    intro i hi
    have hki : αα i + ββ i - nn i - 1 = (k : ℂ) := (Finset.mem_filter.mp hi).2
    have h := hH (ins i) (nn i) τ ⟨-(k : ℤ), by
      rw [hinsκ i]; push_cast; rw [← hki]; ring⟩
    rw [hinsa i, hinsb i] at h
    rw [← h]
    refine Finset.sum_congr rfl fun z _ => ?_
    exact congrArg (fun u => coef z * traceFun D.Mfam D.h z u τ)
      (map_bvec F D a b (vacuumLW W hv) c.ε (nn i) (ww i) (xx i))
  -- conclude
  have hL : ∑ i ∈ kept αα ββ nn (k : ℂ), cs i *
      ∑ z, coef z * traceFun D.Mfam D.h z (c.ε.val (bvec F D a b (nn i) (ww i) (xx i))) τ =
      ∑ z, coef z * traceFun D.Mfam D.h z v τ := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun z _ => ?_
    obtain ⟨ℓ, hℓ⟩ := traceFun_linear hNice D z τ
    have : ∑ i ∈ kept αα ββ nn (k : ℂ), cs i * (coef z * traceFun D.Mfam D.h z
        (c.ε.val (bvec F D a b (nn i) (ww i) (xx i))) τ) =
        coef z * ∑ i ∈ kept αα ββ nn (k : ℂ), cs i *
          ℓ (c.ε.val (bvec F D a b (nn i) (ww i) (xx i))) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [hℓ]; ring
    rw [this, sum_linear ℓ]
    erw [hε]
    rw [hℓ]
  have hR : ∑ i ∈ kept αα ββ nn (k : ℂ), cs i * ∑ l, lam l * genTerm (G l) (ins i) (nn i) τ =
      0 := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun l _ => ?_
    have : ∑ i ∈ kept αα ββ nn (k : ℂ), cs i * (lam l * genTerm (G l) (ins i) (nn i) τ) =
        lam l * ∑ i ∈ kept αα ββ nn (k : ℂ), cs i * genTerm (G l) (ins i) (nn i) τ := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [this, hgen, mul_zero]
  rw [← hL, Finset.sum_congr rfl fun i hi => by rw [hHi i hi], hR]

/-- **`TraceSeparationInput` is discharged.** -/
theorem traceSeparationInput_holds : TraceSeparationInput.{u, w} := by
  intro 𝒱 _ _ W hNice ι _ _ D _ hirr _ F a b c hv η' hη'
  exact traceSeparation_holds F D a b hNice hirr c hv η' hη'

/-- **Huang's Theorem 5.2 (`FusionEigenInput`).** -/
theorem fusionEigenInput_holds : VOA.Huang.VerlindeEigen.FusionEigenInput.{u, w} :=
  VOA.Huang.GenusOneG1e.fusionEigenInput_of_algebraic intertwinerSubstitutionInput_holds
    traceSkewInput_holds traceSeparationInput_holds

end Final

end VOA.Huang.GenusOneG1f
