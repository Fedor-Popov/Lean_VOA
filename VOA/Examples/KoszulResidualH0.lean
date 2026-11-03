/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Examples.KoszulResidualEval

/-!
# Koszul `H₀` of the actual `d_K`: the boundaries are the kernel of the symbol evaluation

On the antighost-free blocks of the actual relative complex, a vector is a `d_K`-boundary iff
its symbol evaluation `EV = ev ⊗ 1` vanishes (`range_comp_eq`). Generic part:
`h0_of_native` (from a native homotopy and an evaluation `EV` with `EV ∘ d = 0` and no common
kernel with `Δ` on the antighost-free blocks).

Everything is proved outright from `hA`.
-/

set_option linter.deprecated false

namespace VOA.KoszulResidual

open VOA.ConcreteHodge VOA.GradedUnitaryCohomology VOA.VertexOperatorAlgebra
open Sl2CosetConcrete Sl2SemiInfinite AffineSl2GeneralRigidity AffineSl2BelowCritical
open VOA.LeeYangTransferAssembly VOA.KoszulConcrete MvPolynomial
open scoped TensorProduct

noncomputable section

/-! ### Generic Koszul `H₀` -/

/-- **Generic Koszul `H₀` from a native homotopy.** -/
theorem h0_of_native {E K F : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup K]
    [Module ℂ K] [FiniteDimensional ℂ K] [AddCommGroup F] [Module ℂ F]
    {C : KahlerComplex K} (B : KoszulBlocks C)
    (ι : K →ₗ[ℂ] E) (hι : Function.Injective ι) (d h Δ : E →ₗ[ℂ] E) (EV : E →ₗ[ℂ] F)
    (H1 : ∀ (a c : ℤ × ℤ), a + shQm = c → ∀ (q q' : ℤ), q' + 1 = q → ∀ x : B.blk (a, q),
      ι (B.comp a c q q' x : K) = d (ι (x : K)))
    (H2 : ∀ (a b : ℤ × ℤ), b + shQm = a → ∀ (q q1 : ℤ), q + 1 = q1 →
      ∀ v ∈ (B.blk (a, q)).map ι, h v ∈ (B.blk (b, q1)).map ι)
    (H3 : ∀ v, d (h v) + h (d v) = Δ v)
    (HEVd : ∀ v, EV (d v) = 0)
    (Hinj : ∀ (c : ℤ × ℤ), ∀ v ∈ (B.blk (c, ((0 : ℕ) : ℤ))).map ι, Δ v = 0 → EV v = 0 → v = 0)
    {b c : ℤ × ℤ} (hb : b + shQm = c) (x : B.blk (c, ((0 : ℕ) : ℤ))) :
    x ∈ LinearMap.range (B.comp b c ((0 + 1 : ℕ) : ℤ) ((0 : ℕ) : ℤ)) ↔ EV (ι (x : K)) = 0 := by
  -- `d` vanishes on the antighost-free blocks
  have hd0 : ∀ (c : ℤ × ℤ), ∀ v ∈ (B.blk (c, ((0 : ℕ) : ℤ))).map ι, d v = 0 := by
    intro c v hv
    obtain ⟨u, hu, rfl⟩ := hv
    rw [← H1 c (c + shQm) rfl ((0 : ℕ) : ℤ) (-1) (by simp) ⟨u, hu⟩]
    have h0 : (((B.comp c (c + shQm) ((0 : ℕ) : ℤ) (-1)) ⟨u, hu⟩ : B.blk _) : K) = 0 :=
      (Submodule.eq_bot_iff _).mp (B.neg _ (-1) (by norm_num)) _ (Submodule.coe_mem _)
    rw [h0, map_zero]
  constructor
  · rintro ⟨u, rfl⟩
    rw [H1 b c hb _ _ (by simp) u, HEVd]
  · intro hx
    -- `Δ` preserves `W ∩ ker EV`
    set W := (B.blk (c, ((0 : ℕ) : ℤ))).map ι
    let K0 : Submodule ℂ E := W ⊓ LinearMap.ker EV
    have hΔW : ∀ v ∈ W, Δ v ∈ W := by
      intro v hv
      rw [← H3, hd0 c v hv, map_zero, add_zero]
      obtain ⟨u, hu, hu'⟩ := H2 c b hb _ ((0 : ℕ) + 1 : ℤ) rfl v hv
      rw [← hu', ← H1 b c hb _ ((0 : ℕ) : ℤ) rfl ⟨u, hu⟩]
      exact ⟨_, (B.comp b c _ _ ⟨u, hu⟩).2, rfl⟩
    have hK0 : ∀ v ∈ K0, Δ v ∈ K0 := by
      intro v hv
      refine ⟨hΔW v hv.1, ?_⟩
      show EV (Δ v) = 0
      rw [← H3, hd0 c v hv.1, map_zero, add_zero, HEVd]
    haveI : FiniteDimensional ℂ W := Module.Finite.map _ _
    haveI : FiniteDimensional ℂ K0 := Submodule.finiteDimensional_of_le inf_le_left
    obtain ⟨z, hzK, hz⟩ := exists_preimage_of_injOn K0 Δ hK0
      (fun v hv hv0 => Hinj c v hv.1 hv0 hv.2) (ι (x : K)) ⟨⟨x, x.2, rfl⟩, hx⟩
    obtain ⟨u, hu, hu'⟩ := H2 c b hb _ ((0 : ℕ) + 1 : ℤ) rfl z hzK.1
    have hq : ((0 : ℕ) + 1 : ℤ) = ((0 + 1 : ℕ) : ℤ) := by simp
    rw [hq] at hu
    refine ⟨⟨u, hu⟩, ?_⟩
    apply Subtype.ext
    apply hι
    rw [H1 b c hb _ _ (by simp) ⟨u, hu⟩]
    change d (ι u) = ι (x : K)
    rw [hu', ← hz, ← H3, hd0 c z hzK.1, map_zero, add_zero]

/-! ### Letters of small weight -/

theorem letterWt_le_enOf {μ : CurrentIndex} {q : LexLetter} (hq : μ q ≠ 0) :
    letterWt q ≤ enOf μ := by
  rw [enOf, Finsupp.weight_apply, Finsupp.sum]
  have hmem : q ∈ μ.support := Finsupp.mem_support_iff.mpr hq
  calc letterWt q ≤ μ q • letterWt q := by
        rw [smul_eq_mul]; exact Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hq)
    _ ≤ ∑ i ∈ μ.support, μ i • letterWt i :=
        Finset.single_le_sum (f := fun i => μ i • letterWt i) (fun _ _ => Nat.zero_le _) hmem

theorem sdeg_eq_degree {N : ℕ} {μ : CurrentIndex} (hμ : enOf μ ≤ N) :
    sdeg (sN N) μ = μ.degree := by
  rw [sdeg, Finsupp.degree_apply]
  symm
  refine Finset.sum_subset (fun q hq => ?_) (fun q _ hq => ?_)
  · rw [mem_sN]
    have := letterWt_le_enOf (Finsupp.mem_support_iff.mp hq)
    simp only [letterWt] at this
    omega
  · exact Finsupp.notMem_support_iff.mp hq

/-- The `U`-constant part. -/
def uConst : Module.End ℂ USpace :=
  PhiU.symm.toLinearMap ∘ₗ (homogeneousComponent 0 : MvPolynomial LexLetter ℂ →ₗ[ℂ] _) ∘ₗ
    PhiU.toLinearMap

theorem PhiU_uConst (u : USpace) : PhiU (uConst u) = homogeneousComponent 0 (PhiU u) := by
  simp [uConst]

/-- On a layer of weight `≤ N`, the partial-degree-`0` projection is the constant part. -/
theorem uProj_zero_eq_uConst {N : ℕ} {i : (ℤ × ℤ) × ℂ}
    (hw : ∀ w : ℤ, (w : ℂ) = i.2 → w ≤ N) {u : USpace} (hu : u ∈ uDeg i) :
    uProj (sN N) 0 u = uConst u := by
  by_cases hi : ∃ t m, layerIndex t m = i
  · obtain ⟨t, m, rfl⟩ := hi
    have hmN : m ≤ N := hw m rfl
    apply PhiU.injective
    rw [PhiU_uProj, PhiU_uConst]
    ext μ
    rw [coeff_sProj, coeff_homogeneousComponent]
    by_cases hμ : μ ∈ (PhiU u).support
    · obtain ⟨-, hen⟩ := PhiU_support_of_mem hu μ hμ
      rw [sdeg_eq_degree (by omega)]
    · rw [notMem_support_iff.mp hμ]; simp
  · push Not at hi
    rw [uDeg_eq_bot_of hi, Submodule.mem_bot] at hu
    rw [hu, map_zero, map_zero]

theorem abDeg_le_weight (j : (ℤ × ℤ) × ℂ) : tensorDeg aDeg bDeg j ≤ abSVA.grading j.2 := by
  refine tensorDeg_le wtIndex _ _ ASVA.grading BSVA.grading abSVA.grading ?_ ?_ ?_ j
  · intro k k' x y hx hy
    exact TensorVA.tmul_mem_tenGrading ASVA BSVA hx (by rwa [add_sub_cancel_left])
  · intro l; exact layerDeg_le_gradingC _ _ l
  · intro l; exact trivialDeg_le_gradingC l

theorem mProj_zero_eq_mConst {N : ℕ} {i : (ℤ × ℤ) × ℂ} {w : ℕ} (hwi : (w : ℂ) = i.2)
    (hwN : w ≤ N) :
    ∀ m ∈ matterDeg i, mProj (sN N) 0 m = TensorProduct.map LinearMap.id uConst m := by
  refine tensorDeg_induction (tensorDeg aDeg bDeg) uDeg i _ (by simp)
    (fun x y hx hy => by beta_reduce at hx hy ⊢; rw [map_add, map_add, hx, hy])
    (fun c x hx => by beta_reduce at hx ⊢; rw [map_smul, map_smul, hx]) ?_
  intro b xy hxy u hu
  by_cases hxy0 : xy = 0
  · subst hxy0; simp
  have hb : ∃ w1 : ℕ, (w1 : ℂ) = b.2 := by
    by_contra h
    have h1 := abDeg_le_weight b hxy
    rw [abNatSupported _ (by rintro ⟨w1, hw1⟩; exact h ⟨w1, hw1⟩), Submodule.mem_bot] at h1
    exact hxy0 h1
  obtain ⟨w1, hw1⟩ := hb
  simp only [mProj, TensorProduct.map_tmul, LinearMap.id_apply]
  congr 1
  refine uProj_zero_eq_uConst (fun w' hw' => ?_) hu
  simp only [Prod.snd_sub, ← hwi, ← hw1] at hw'
  have : (w' : ℤ) = w - w1 := by exact_mod_cast hw'
  omega

/-! ### The evaluation on the BRST space -/

section EVB

variable (hA : GradedUnitary affineForm affineRealStructure affineFlag)

/-- The symbol evaluation on the BRST space: `ev ⊗ 1`. -/
def EVB : BRSTSpace →ₗ[ℂ] (ASpace ⊗[ℂ] BSpace) ⊗[ℂ] Sl2GhostSpace :=
  TensorProduct.map (ev hA) LinearMap.id

theorem EVB_dN (s : Finset LexLetter) (v : BRSTSpace) : EVB hA (dN hA s v) = 0 := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]
  | tmul m g =>
      simp only [dN, LinearMap.coe_sum, Finset.sum_apply, map_sum, TensorProduct.map_tmul,
        EVB, LinearMap.id_apply, ev_mLead, TensorProduct.zero_tmul, Finset.sum_const_zero]

/-- The embedding of `A ⊗ B` as the `U`-vacuum part. -/
def jU : ASpace ⊗[ℂ] BSpace →ₗ[ℂ] MatterSpace :=
  (TensorProduct.mk ℂ (ASpace ⊗[ℂ] BSpace) USpace).flip (PhiU.symm 1)

theorem uConst_eq (u : USpace) : uConst u = coeff 0 (PhiU u) • PhiU.symm 1 := by
  apply PhiU.injective
  rw [PhiU_uConst, map_smul, LinearEquiv.apply_symm_apply, homogeneousComponent_zero,
    smul_eq_C_mul, mul_one]

theorem ev_one (xy : ASpace ⊗[ℂ] BSpace) : ev hA (xy ⊗ₜ[ℂ] PhiU.symm 1) = xy := by
  rw [ev_tmul, evU_apply, LinearEquiv.apply_symm_apply, map_one, Subalgebra.coe_one,
    Module.End.one_eq_id, LinearMap.rTensor_id, LinearMap.id_apply]

/-- **The `U`-constant part factors through `ev`.** -/
theorem mConst_factor (m : MatterSpace) :
    TensorProduct.map LinearMap.id uConst m =
      jU (ev hA (TensorProduct.map LinearMap.id uConst m)) := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add]; rw [← hx, ← hy]
  | tmul xy u =>
      rw [TensorProduct.map_tmul, LinearMap.id_apply, uConst_eq, TensorProduct.tmul_smul,
        map_smul, map_smul, ev_one]
      rfl

/-! ### The partial-degree projections on the BRST space -/

/-- The partial-degree projection on the BRST space. -/
def mProjB (N d : ℕ) : Module.End ℂ BRSTSpace :=
  TensorProduct.map (mProj (sN N) d) LinearMap.id

theorem mProjB_mL (N d : ℕ) (v : BRSTSpace) :
    mProjB N d (TensorProduct.map (mL hA (sN N)) LinearMap.id v) =
      (d : ℂ) • mProjB N d v +
        TensorProduct.map (mLA hA (sN N)) LinearMap.id (mProjB N (d + 1) v) := by
  have h := mProj_mL hA (sN N) d
  simp only [mProjB, ← LinearMap.comp_apply, ← TensorProduct.map_comp, h,
    LinearMap.id_comp, TensorProduct.map_add_left, TensorProduct.map_smul_left,
    LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_id]

theorem exists_mProjB_bound (N : ℕ) (v : BRSTSpace) :
    ∃ D : ℕ, (∀ d, D < d → mProjB N d v = 0) ∧
      ∑ d ∈ Finset.range (D + 1), mProjB N d v = v := by
  have key : ∃ D : ℕ, ∀ D', D ≤ D' → (∀ d, D' < d → mProjB N d v = 0) ∧
      ∑ d ∈ Finset.range (D' + 1), mProjB N d v = v := by
    induction v using TensorProduct.induction_on with
    | zero => exact ⟨0, fun _ _ => ⟨fun _ _ => map_zero _, by simp⟩⟩
    | tmul m g =>
        obtain ⟨D, hD⟩ := exists_mProj_bound (sN N) m
        refine ⟨D, fun D' hD' => ⟨fun d hd => ?_, ?_⟩⟩
        · rw [mProjB, TensorProduct.map_tmul, (hD D' hD').1 d hd, TensorProduct.zero_tmul]
        · simp only [mProjB, TensorProduct.map_tmul, LinearMap.id_apply, ← TensorProduct.sum_tmul]
          rw [(hD D' hD').2]
    | add v w hv hw =>
        obtain ⟨D1, h1⟩ := hv
        obtain ⟨D2, h2⟩ := hw
        refine ⟨max D1 D2, fun D' hD' => ⟨fun d hd => ?_, ?_⟩⟩
        · rw [map_add, (h1 D' (le_of_max_le_left hD')).1 d hd,
            (h2 D' (le_of_max_le_right hD')).1 d hd, add_zero]
        · simp only [map_add, Finset.sum_add_distrib]
          rw [(h1 D' (le_of_max_le_left hD')).2, (h2 D' (le_of_max_le_right hD')).2]
  obtain ⟨D, hD⟩ := key
  exact ⟨D, hD D le_rfl⟩

set_option maxHeartbeats 1000000 in
/-- The weight lemma on joint pieces of weight `≤ N`. -/
theorem mProjB_zero_eq (N : ℕ) {q0 : ℤ} {v : BRSTSpace} (hv : v ∈ lapSup N q0) :
    mProjB N 0 v = TensorProduct.map (TensorProduct.map LinearMap.id uConst) LinearMap.id v := by
  refine Submodule.iSup_induction _ (motive := fun v => mProjB N 0 v =
    TensorProduct.map (TensorProduct.map LinearMap.id uConst) LinearMap.id v) hv ?_ (by simp)
    (fun x y hx hy => by beta_reduce at hx hy ⊢; rw [map_add, map_add, hx, hy])
  intro j y hy
  refine Submodule.iSup_induction _ (motive := fun v => mProjB N 0 v =
    TensorProduct.map (TensorProduct.map LinearMap.id uConst) LinearMap.id v) hy ?_ (by simp)
    (fun x y hx hy => by beta_reduce at hx hy ⊢; rw [map_add, map_add, hx, hy])
  intro hj z hz
  obtain ⟨-, n0, hn0, hw⟩ := hj
  refine tensorDeg_induction KoszulConcrete.matterB KoszulConcrete.ghostB j
    (fun z => mProjB N 0 z =
      TensorProduct.map (TensorProduct.map LinearMap.id uConst) LinearMap.id z) (by simp)
    (fun x y hx hy => by beta_reduce at hx hy ⊢; rw [map_add, map_add, hx, hy])
    (fun c x hx => by beta_reduce at hx ⊢; rw [map_smul, map_smul, hx]) ?_ z hz
  intro b m hm g hg
  beta_reduce
  by_cases hm0 : m = 0
  · rw [hm0, TensorProduct.zero_tmul, map_zero, map_zero]
  by_cases hg0 : g = 0
  · rw [hg0, TensorProduct.tmul_zero, map_zero, map_zero]
  obtain ⟨wm, hwm⟩ := matterB_nat hm hm0
  obtain ⟨wg, hwg⟩ := ghostB_nat hg hg0
  have hsum : (wm : ℤ) + wg = n0 := by
    have : (j.1.1.2 : ℂ) = b.1.1.2 + (j - b).1.1.2 := by simp
    rw [hw, ← hwm, ← hwg] at this
    exact_mod_cast this.symm
  have hmD : m ∈ matterDeg b.1.1 := by
    unfold KoszulConcrete.matterB matterF at hm
    split_ifs at hm
    · exact hm
    all_goals exact absurd ((Submodule.mem_bot ℂ).mp hm) hm0
  simp only [mProjB, TensorProduct.map_tmul, LinearMap.id_apply]
  rw [mProj_zero_eq_mConst (w := wm) hwm (by omega) m hmD]

/-- **No common kernel of `ΔN` and `EVB` on the antighost-free blocks.** -/
theorem ΔN_EVB_injective (N : ℕ) {v : BRSTSpace} (hv : v ∈ lapSup N 0)
    (h1 : ΔN hA (sN N) v = 0) (h2 : EVB hA v = 0) : v = 0 := by
  have hNb := NbB_lapSup N 0 hv
  rw [Int.cast_zero, zero_smul] at hNb
  have hL : TensorProduct.map (mL hA (sN N)) LinearMap.id v = 0 := by
    rw [ΔN, LinearMap.add_apply, hNb, add_zero] at h1; exact h1
  obtain ⟨D, hD1, hD2⟩ := exists_mProjB_bound N v
  have hstep : ∀ d, 1 ≤ d → mProjB N (d + 1) v = 0 → mProjB N d v = 0 := by
    intro d hd hnext
    have h := mProjB_mL hA N d v
    rw [hL, map_zero, hnext, map_zero, add_zero] at h
    have hne : (d : ℂ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
    exact eq_zero_of_smul_eq_zero hne h.symm
  have hall : ∀ k d, 1 ≤ d → D + 1 ≤ d + k → mProjB N d v = 0 := by
    intro k
    induction k with
    | zero => intro d _ hd; exact hD1 d (by omega)
    | succ k ih =>
        intro d hd1 hd
        by_cases h : D + 1 ≤ d + k
        · exact ih d hd1 h
        · exact hstep d hd1 (ih (d + 1) (by omega) (by omega))
  have hv0 : v = mProjB N 0 v := by
    conv_lhs => rw [← hD2]
    rw [Finset.sum_eq_single 0 (fun d _ hd => hall (D + 1) d (by omega) (by omega))
      (by simp)]
  rw [hv0, mProjB_zero_eq N hv]
  -- factor through the evaluation
  have hfac : TensorProduct.map (TensorProduct.map LinearMap.id uConst) LinearMap.id v =
      TensorProduct.map (jU ∘ₗ ev hA ∘ₗ TensorProduct.map LinearMap.id uConst)
        LinearMap.id v := by
    congr 1
    congr 1
    exact LinearMap.ext fun m => mConst_factor hA m
  have hvc : TensorProduct.map (TensorProduct.map LinearMap.id uConst) LinearMap.id v = v := by
    rw [← mProjB_zero_eq N hv, ← hv0]
  have hcomp : ∀ w : BRSTSpace, TensorProduct.map (jU ∘ₗ ev hA ∘ₗ
      TensorProduct.map LinearMap.id uConst) (LinearMap.id : Module.End ℂ Sl2GhostSpace) w =
      TensorProduct.map jU LinearMap.id (EVB hA (TensorProduct.map
        (TensorProduct.map LinearMap.id uConst) LinearMap.id w)) := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add, hx, hy, map_add, map_add, map_add]
    | tmul m g => simp [EVB]
  rw [hfac, hcomp, hvc, h2, map_zero]

end EVB

/-! ### Koszul `H₀` of the actual blocks -/

variable (hA : GradedUnitary affineForm affineRealStructure affineFlag) in
/-- **Koszul `H₀` on the actual antighost-free blocks**: a block vector is a `d_K`-boundary
iff its symbol evaluation vanishes. -/
theorem range_comp_iff {n : ℤ} (hp : IsPosOn ((endpointKahler hA).geometry n).P ⊤)
    {b c : ℤ × ℤ} (hb : b + shQm = c) (x : (endpointBlocks hA n hp).blk (c, ((0 : ℕ) : ℤ))) :
    x ∈ LinearMap.range ((endpointBlocks hA n hp).comp b c ((0 + 1 : ℕ) : ℤ) ((0 : ℕ) : ℤ)) ↔
      EVB hA ((x : relativeWeight n) : BRSTSpace) = 0 :=
  h0_of_native (endpointBlocks hA n hp) (relativeWeight n).subtype Subtype.val_injective
    (dN hA (sN n.toNat)) (hN (sN n.toNat)) (ΔN hA (sN n.toNat)) (EVB hA)
    (fun a c hc q q' hq x => comp_coe_eq_dN' hA hp hc hq x)
    (fun a b hb q q1 hq v hv => hN_mem_blkW hA hp hb hq hv)
    (dN_hN_add hA _) (EVB_dN hA _)
    (fun c v hv hv0 hev => ΔN_EVB_injective hA n.toNat
      (by have := goodSup_le_lapSup (blkW_le_goodSup hA hp _ hv); simpa using this) hv0 hev)
    hb x

end

end VOA.KoszulResidual
