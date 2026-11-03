import VOA.Huang.GenusTwoPointSepGeometricFlow

/-! # Finite weight truncations of the full geometric flow -/
noncomputable section
namespace VOA.Huang.GenusTwoPoint.Separate
open VOA GenusOne
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V] {W : VertexOperatorAlgebra V}

/-- Every sufficiently positive Virasoro mode vanishes on a whole weight truncation. -/
theorem positiveVirasoro_zero_on_level (P : LWModule W) {d : ℤ} {k : ℕ}
    (hdk : d ≤ k) {x : P.carrier} (hx : x ∈ moduleLevelLE P d) :
    mode (P.isMod.YM W.conformalVector) ((k : ℤ) + 2) x = 0 := by
  induction hx using Submodule.iSup_induction' with
  | mem j y hy =>
    have hm := mode_mem_weight P.isMod W.conformal_mem hy ((k : ℤ) + 2)
    have he : P.h + ((j : ℤ) : ℂ) + ((2 : ℤ) : ℂ) - (((k : ℤ) + 2 : ℤ) : ℂ) - 1 =
        P.h + (((j : ℤ) - ((k : ℤ) + 1) : ℤ) : ℂ) := by push_cast; ring
    rw [he, LWBottomRecovery.weight_neg_eq_bot P (by have := j.2; omega)] at hm
    exact hm
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]

/-- The generator jet is exact on any smaller weight truncation. -/
theorem moduleCoordGen_jet_on_level (P : LWModule W) (a : ℕ → ℂ)
    {d : ℤ} {K : ℕ} (hdK : d ≤ K) {x : P.carrier} (hx : x ∈ moduleLevelLE P d) :
    moduleCoordGen P (coordinateJet a K) x = moduleCoordGen P a x := by
  change (∑ᶠ k, coordinateJet a K k • _) = ∑ᶠ k, a k • _
  apply finsum_congr
  intro k
  by_cases hk : k < K
  · simp only [coordinateJet, if_pos hk]
  · rw [positiveVirasoro_zero_on_level P (le_trans hdK (by omega)) hx]
    simp only [smul_zero]

/-- Local nilpotent exponentials agree when their generators agree on an
invariant submodule. This includes the inverse exponential by changing signs. -/
theorem expFun_eq_on_invariant {M : Type*} [AddCommGroup M] [Module ℂ M]
    {D E : Module.End ℂ M} (hD : IsLocNilp D) (hE : IsLocNilp E)
    (S : Submodule ℂ M) (hE_mem : ∀ x ∈ S, E x ∈ S)
    (hDE : ∀ x ∈ S, D x = E x) {x : M} (hx : x ∈ S) :
    expFun hD x = expFun hE x := by
  have hm : ∀ r : ℕ, (E ^ r) x ∈ S := by
    intro r
    induction r with
    | zero => exact hx
    | succ r ih => rw [VOA.pow_succ'_apply]; exact hE_mem _ ih
  have hp : ∀ r : ℕ, (D ^ r) x = (E ^ r) x := by
    intro r
    induction r with
    | zero => rfl
    | succ r ih => rw [VOA.pow_succ'_apply, VOA.pow_succ'_apply, ih, hDE _ (hm r)]
  rw [expFun_eq_finsum_linearFlowCoeff hD, expFun_eq_finsum_linearFlowCoeff hE]
  exact finsum_congr fun r => by simp only [linearFlowCoeff, hp]

/-- Huang's coordinate exponential, and not merely its generator, stabilizes
on each finite weight truncation. -/
theorem moduleCoordinateChange_jet_on_level (P : LWModule W) (a : ℕ → ℂ)
    {d : ℤ} {K : ℕ} (hdK : d ≤ K) {x : P.carrier} (hx : x ∈ moduleLevelLE P d) :
    moduleCoordinateChange P (coordinateJet a K) x = moduleCoordinateChange P a x := by
  apply expFun_eq_on_invariant (moduleCoordGen_isLocNilp P _).neg
    (moduleCoordGen_isLocNilp P _).neg (moduleLevelLE P d) _ _ hx
  · intro y hy
    exact Submodule.neg_mem _ (moduleLevelLE_mono P (by omega)
      (moduleCoordGen_mem_lower P a hy))
  · intro y hy
    change -(moduleCoordGen P (coordinateJet a K) y) = -(moduleCoordGen P a y)
    rw [moduleCoordGen_jet_on_level P a hdK hy]

theorem moduleCoordinateChange_symm_jet_on_level (P : LWModule W) (a : ℕ → ℂ)
    {d : ℤ} {K : ℕ} (hdK : d ≤ K) {x : P.carrier} (hx : x ∈ moduleLevelLE P d) :
    (moduleCoordinateChange P (coordinateJet a K)).symm x =
      (moduleCoordinateChange P a).symm x := by
  change expFun (moduleCoordGen_isLocNilp P (coordinateJet a K)).neg.neg x =
    expFun (moduleCoordGen_isLocNilp P a).neg.neg x
  simp only [neg_neg]
  apply expFun_eq_on_invariant (moduleCoordGen_isLocNilp P _)
    (moduleCoordGen_isLocNilp P _) (moduleLevelLE P d) _ _ hx
  · intro y hy
    exact moduleLevelLE_mono P (by omega) (moduleCoordGen_mem_lower P a hy)
  · intro y hy
    exact moduleCoordGen_jet_on_level P a hdK hy

private theorem expFun_generator_congr {M : Type*} [AddCommGroup M] [Module ℂ M]
    {D E : Module.End ℂ M} (h : D = E) (hD : IsLocNilp D) (hE : IsLocNilp E) (x : M) :
    expFun hD x = expFun hE x := by subst E; rfl

/-- The finite geometric flow computes the actual normalized sandwich.
One cutoff works for every larger jet for the specified mode and vectors.
No common nilpotence bound on the infinite-dimensional field space is asserted. -/
theorem normalizedIntertwiner_eq_geometricJet
    {P Q N : LWModule W} (Y : IntertwiningOperator P.isMod Q.isMod N.isMod)
    (n : ℂ) (w : P.carrier) (x : Q.carrier) :
    ∃ K₀ : ℕ, ∀ K ≥ K₀,
      normalizedCoordinateChange N
        (Y.val n w ((normalizedCoordinateChange Q).symm x)) =
      ∑ᶠ r, linearFlowCoeff
        (geometricJet (fun j => -iterativeLog (logarithmicCoordinate 1) j) K)
        (fun m v => Y.val m v) r n w x := by
  let a := iterativeLog (logarithmicCoordinate 1)
  obtain ⟨d, hd⟩ := exists_mem_moduleLevelLE Q x
  obtain ⟨e, he⟩ := exists_mem_moduleLevelLE N
    (Y.val n w ((normalizedCoordinateChange Q).symm x))
  refine ⟨max d.toNat e.toNat, fun K hK => ?_⟩
  have hdK : d ≤ (K : ℤ) := by omega
  have heK : e ≤ (K : ℤ) := by omega
  have hneg (R : LWModule W) :
      moduleCoordGen R (coordinateJet (fun j => -a j) K) =
        -moduleCoordGen R (coordinateJet a K) := by
    rw [moduleCoordGen_jet, moduleCoordGen_jet]
    simp only [neg_smul, Finset.sum_neg_distrib]
  rw [← intertwiner_geometricJet_evaluate]
  have hs : expFun (moduleCoordGen_isLocNilp Q
      (coordinateJet (fun j => -a j) K)).neg x =
      (moduleCoordinateChange Q a).symm x := by
    refine Eq.trans ?_ (moduleCoordinateChange_symm_jet_on_level Q a hdK hd)
    change expFun _ x = expFun (moduleCoordGen_isLocNilp Q (coordinateJet a K)).neg.neg x
    apply expFun_generator_congr
    rw [hneg]
  have ht : expFun (moduleCoordGen_isLocNilp N
      (coordinateJet (fun j => -a j) K))
      (Y.val n w ((moduleCoordinateChange Q a).symm x)) =
      moduleCoordinateChange N a (Y.val n w ((moduleCoordinateChange Q a).symm x)) := by
    refine Eq.trans ?_ (moduleCoordinateChange_jet_on_level N a heK he)
    change expFun _ _ = expFun (moduleCoordGen_isLocNilp N (coordinateJet a K)).neg _
    exact expFun_generator_congr (hneg N) _ _ _
  change moduleCoordinateChange N a (Y.val n w ((moduleCoordinateChange Q a).symm x)) = _
  change _ = expFun (moduleCoordGen_isLocNilp N (coordinateJet (fun j => -a j) K))
    (Y.val n w (expFun (moduleCoordGen_isLocNilp Q (coordinateJet (fun j => -a j) K)).neg x))
  rw [hs, ht]

end VOA.Huang.GenusTwoPoint.Separate
