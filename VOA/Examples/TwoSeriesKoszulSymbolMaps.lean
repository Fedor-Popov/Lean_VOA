/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.KoszulResidualSymbolMaps
import VOA.Examples.TwoSeriesKoszulSymbol

/-!
# Level-generic port of `KoszulResidualSymbolMaps`
-/

namespace VOA.TwoSeries

open VOA.ConcreteHodge VOA.KoszulResidual VOA.KoszulConcrete VOA.SymbolModel VOA.CyclicEval
open VOA.GradedUnitaryCohomology VOA.VertexOperatorAlgebra Sl2CosetConcrete Sl2SemiInfinite
open AffineSl2GeneralRigidity AffineSl2BelowCritical VOA.LeeYangTransferAssembly VOA.SympFerm
open VOA.Ghost AffineVOA
open scoped TensorProduct

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

universe u v w

variable (L : CosetLevels)

/-! ## Port of `KoszulResidualSymbolMaps` -/


variable (hA : GradedUnitary (affineForm L) (affineRealStructure L) (affineFlag L))

/-- The block projection decomposes an ambient vector. -/
theorem pr_decomp {n : ℤ} (hp : IsPosOn (((endpointKahler L) hA).geometry n).P ⊤)
    (T : (ℤ × ℤ) × ℤ) (y : (relativeWeight L) n) :
    ((((endpointBlocks L) hA n hp).pr T y : (relativeWeight L) n) : (BRSTSpace L)) ∈ (Tsup L) T ∧
      (y : (BRSTSpace L)) - ((((endpointBlocks L) hA n hp).pr T y : (relativeWeight L) n) : (BRSTSpace L)) ∈
        (NTp L) T := by
  obtain ⟨p, hpdef⟩ : ∃ p, p = ((endpointBlocks L) hA n hp).pr T y := ⟨_, rfl⟩
  rw [← hpdef]
  have hp1 : (p : (BRSTSpace L)) ∈ (blkSup L) n (· = T) := by
    rw [hpdef]; exact ((endpointBlocks L) hA n hp).pr_mem T y
  refine ⟨?_, ?_⟩
  · exact (iSup_le fun j => iSup_le fun hj => le_iSup_of_le j (le_iSup_of_le hj.1 le_rfl) :
      (blkSup L) n (· = T) ≤ (Tsup L) T) hp1
  · have hyp : y - p ∈ ⨆ (b : (ℤ × ℤ) × ℤ) (_ : b ≠ T), (blkE L) n b := by
      rw [hpdef]; exact KoszulBlocks.sub_pr_mem ((endpointBlocks L) hA n hp) T y
    rw [← Submodule.coe_sub]
    refine Submodule.iSup_induction _ (motive := fun v : (relativeWeight L) n => (v : (BRSTSpace L)) ∈
      (NTp L) T) hyp ?_ (by simp) (fun v w hv hw => by
        beta_reduce at hv hw ⊢; rw [Submodule.coe_add]; exact Submodule.add_mem _ hv hw)
    intro b v hv
    refine Submodule.iSup_induction _ (motive := fun v : (relativeWeight L) n => (v : (BRSTSpace L)) ∈
      (NTp L) T) hv ?_ (by simp) (fun v w hv hw => by
        beta_reduce at hv hw ⊢; rw [Submodule.coe_add]; exact Submodule.add_mem _ hv hw)
    intro hb u hu
    have hu' : (u : (BRSTSpace L)) ∈ (blkSup L) n (· = b) := hu
    have hle : (blkSup L) n (· = b) ≤ (NTp L) T :=
      iSup_le fun j => iSup_le fun hj => le_iSup_of_le j (le_iSup_of_le
        (Or.inl (by rw [hj.1]; exact hb)) le_rfl)
    exact hle hu'

/-! ### `π₀` -/

section Pi0

variable {n : ℤ} (hp : IsPosOn (((endpointKahler L) hA).geometry n).P ⊤) (r : ℕ)

/-- **`π₀`**: evaluate the vacuum coefficient's auxiliary symbol at `x = -a`, project to
`gr_r A ⊗ L_1`. -/
def π0E : ((endpointBlocks L) hA n hp).blk (aR r, ((0 : ℕ) : ℤ)) →ₗ[ℂ] (GrA L) r ⊗[ℂ] BSpace :=
  (PiR L) hA r ∘ₗ (ev L) hA ∘ₗ (extM L) ∘ₗ ((relativeWeight L) n).subtype ∘ₗ
    (((endpointBlocks L) hA n hp).blk (aR r, ((0 : ℕ) : ℤ))).subtype

theorem π0E_apply (x : ((endpointBlocks L) hA n hp).blk (aR r, ((0 : ℕ) : ℤ))) :
    (π0E L) hA hp r x = (PiR L) hA r ((ev L) hA ((extM L) ((x : (relativeWeight L) n) : (BRSTSpace L)))) := rfl

theorem π0E_eq_zero_iff (x : ((endpointBlocks L) hA n hp).blk (aR r, ((0 : ℕ) : ℤ))) :
    (π0E L) hA hp r x = 0 ↔ (EVB L) hA ((x : (relativeWeight L) n) : (BRSTSpace L)) = 0 := by
  obtain ⟨hx1, hx2⟩ := (blk_vacForm L) hA (n := n) (a := aR r) rfl (x : (relativeWeight L) n) x.2
  rw [π0E_apply]
  conv_rhs => rw [hx1, EVB_tmul_gvac]
  constructor
  · intro h
    rw [(PiR_injOn L) hA r ((ev_mem L) hA _ _ hx2) h, TensorProduct.zero_tmul]
  · intro h
    rw [(eq_zero_of_tmul_gvac L) h, map_zero]

theorem ker_π0E :
    LinearMap.ker ((π0E L) hA hp r) = LinearMap.range (((endpointBlocks L) hA n hp).comp
      (aR r - shQm) (aR r) ((0 + 1 : ℕ) : ℤ) ((0 : ℕ) : ℤ)) := by
  ext x
  rw [LinearMap.mem_ker, (range_comp_iff L) hA hp (by abel) x, π0E_eq_zero_iff]

theorem π0E_weight (x : ((endpointBlocks L) hA n hp).blk (aR r, ((0 : ℕ) : ℤ))) :
    (π0E L) hA hp r x ∈ tensorWeight ((grDeg L) r) bWeight n := by
  obtain ⟨-, hx2⟩ := (blk_vacForm L) hA (n := n) (a := aR r) rfl (x : (relativeWeight L) n) x.2
  exact (PiR_weight L) hA r n ((ev_mem L) hA _ _ hx2)

end Pi0

/-! ### `π₁` -/

section Pi1

variable {n : ℤ} (hp : IsPosOn (((endpointKahler L) hA).geometry n).P ⊤) (r : ℕ)

/-- **`π₁`**: the `c^c_{-k}`-coefficient, evaluated as for `π₀`. -/
def π1E : ((endpointBlocks L) hA n hp).blk (aR r + shQm, ((0 : ℕ) : ℤ)) →ₗ[ℂ]
    (Fin 3 × ℕ → (GrA L) r ⊗[ℂ] BSpace) :=
  LinearMap.pi fun k => (PiR L) hA r ∘ₗ (ev L) hA ∘ₗ (extM L) ∘ₗ
    TensorProduct.map LinearMap.id (bAn k.1 k.2) ∘ₗ ((relativeWeight L) n).subtype ∘ₗ
      (((endpointBlocks L) hA n hp).blk (aR r + shQm, ((0 : ℕ) : ℤ))).subtype

theorem π1E_apply (y : ((endpointBlocks L) hA n hp).blk (aR r + shQm, ((0 : ℕ) : ℤ)))
    (k : Fin 3 × ℕ) :
    (π1E L) hA hp r y k = (PiR L) hA r ((ev L) hA ((extM L) (TensorProduct.map LinearMap.id (bAn k.1 k.2)
      ((y : (relativeWeight L) n) : (BRSTSpace L))))) := rfl

theorem π1E_apply' (y : ((endpointBlocks L) hA n hp).blk (aR r + shQm, ((0 : ℕ) : ℤ)))
    (c : Fin 3) (kk : ℕ) :
    (π1E L) hA hp r y (c, kk) = (PiR L) hA r ((ev L) hA ((extM L) (TensorProduct.map LinearMap.id (bAn c kk)
      ((y : (relativeWeight L) n) : (BRSTSpace L))))) := rfl

theorem EVB_mapG (G : Module.End ℂ Sl2GhostSpace) (v : (BRSTSpace L)) :
    (EVB L) hA (TensorProduct.map LinearMap.id G v) = TensorProduct.map LinearMap.id G ((EVB L) hA v) := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul m g => simp [EVB]

theorem map_NT_eq (T : Finset (Fin 3 × (ℕ × Fin 2))) (v : ((ASpace L) ⊗[ℂ] BSpace) ⊗[ℂ] Sl2GhostSpace) :
    TensorProduct.map LinearMap.id (NT T) v = ∑ t ∈ T, TensorProduct.map LinearMap.id
      (ConcreteHodge.Cr t.1 t.2) (TensorProduct.map LinearMap.id (ConcreteHodge.An t.1 t.2) v) := by
  rw [NT, map_id_sum, LinearMap.coe_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [← LinearMap.comp_apply, ← TensorProduct.map_comp, LinearMap.id_comp]

theorem π1E_eq_zero_iff (y : ((endpointBlocks L) hA n hp).blk (aR r + shQm, ((0 : ℕ) : ℤ))) :
    (π1E L) hA hp r y = 0 ↔ (EVB L) hA ((y : (relativeWeight L) n) : (BRSTSpace L)) = 0 := by
  obtain ⟨hy1, hy2⟩ := (blk_oneC L) hA (n := n) (a := aR r + shQm) (by simp [shQm])
    (y : (relativeWeight L) n) y.2
  constructor
  · intro h
    have hk : ∀ (c : Fin 3) (kk : ℕ), (EVB L) hA (TensorProduct.map LinearMap.id (bAn c kk)
        ((y : (relativeWeight L) n) : (BRSTSpace L))) = 0 := by
      intro c kk
      rcases Nat.eq_zero_or_pos kk with rfl | hkk
      · rw [bAnB_zero_rel, map_zero]
      · obtain ⟨hP, hD⟩ := hy2 c kk hkk
        have h0 := congrFun h (c, kk)
        rw [π1E_apply, Pi.zero_apply] at h0
        have hD' : (extM L) (TensorProduct.map LinearMap.id (bAn c kk)
            ((y : (relativeWeight L) n) : (BRSTSpace L))) ∈ (matterDeg L) ((aR r, ((n - kk : ℤ) : ℂ))) := by
          convert hD using 2
          simp [aR, shQm]
        have hev := (PiR_injOn L) hA r ((ev_mem L) hA _ _ hD') h0
        rw [← hP, map_Pvac_eq, EVB_tmul_gvac, hev, TensorProduct.zero_tmul]
    rw [← hy1, EVB_mapG, map_NT_eq]
    refine Finset.sum_eq_zero fun t ht => ?_
    obtain ⟨c, kk, e⟩ := t
    have he : e = 1 := (mem_Tc.mp ht).2
    subst he
    rw [← EVB_mapG]
    change TensorProduct.map LinearMap.id (ConcreteHodge.Cr c (kk, 1))
      ((EVB L) hA (TensorProduct.map LinearMap.id (bAn c kk) ((y : (relativeWeight L) n) : (BRSTSpace L)))) = 0
    rw [hk c kk, map_zero]
  · intro h
    funext k
    have h0 : (EVB L) hA (TensorProduct.map LinearMap.id (bAn k.1 k.2)
        ((y : (relativeWeight L) n) : (BRSTSpace L))) = 0 := by
      rw [EVB_mapG, h, map_zero]
    show (π1E L) hA hp r y k = 0
    rw [π1E_apply, ev_extM_eq_ext, h0, map_zero, map_zero, map_zero]

theorem ker_π1E :
    LinearMap.ker ((π1E L) hA hp r) = LinearMap.range (((endpointBlocks L) hA n hp).comp
      (aR r) (aR r + shQm) ((0 + 1 : ℕ) : ℤ) ((0 : ℕ) : ℤ)) := by
  ext y
  rw [LinearMap.mem_ker, (range_comp_iff L) hA hp rfl y, π1E_eq_zero_iff]

end Pi1

/-! ### The intertwining -/

section Inter

variable {n : ℤ} (hp : IsPosOn (((endpointKahler L) hA).geometry n).P ⊤) (r : ℕ)

theorem grDiag_PiR_ev (c : Fin 3) (kk : ℕ) {m : (MatterSpace L)} (hm : m ∈ (matterDeg L) (aR r, (n : ℂ))) :
    (grDiag L) r (c, kk) ((PiR L) hA r ((ev L) hA m)) = (PiR L) hA r ((ev L) hA ((mPos L) hA c kk m)) := by
  have hev := (ev_mem L) hA _ m hm
  rw [ev_mPos, map_add, (PiR_aPos L) hA r c kk hev, PiR_bMode, grDiag, LinearMap.add_apply]

theorem mMode_zero_of_rel (c : Fin 3) (x : (relativeWeight L) n) {m : (MatterSpace L)}
    (hx : (x : (BRSTSpace L)) = m ⊗ₜ[ℂ] gvac) : (mMode L) c 0 m = 0 := by
  have h := ((mem_relativeCarrier _ _).mp x.2.1).1 c
  rw [hx, totalZero_tmul', show Jz c gvac = 0 from Jz_vacuum c, TensorProduct.tmul_zero,
    add_zero] at h
  exact (eq_zero_of_tmul_gvac' L) h

set_option maxHeartbeats 1000000 in
/-- The `d_CE` component is the `(a + shQm, 0)` block projection of `Q x`. -/
theorem dCE_facts (a : ℤ × ℤ) (x : ((endpointBlocks L) hA n hp).blk (a, ((0 : ℕ) : ℤ))) :
    ((((endpointBlocks L) hA n hp).comp a (a + shQm) ((0 : ℕ) : ℤ) ((0 : ℕ) : ℤ) x :
        (relativeWeight L) n) : (BRSTSpace L)) ∈ (Tsup L) (a + shQm, ((0 : ℕ) : ℤ)) ∧
      semiInfiniteQ (matterAction L).toAffineSl2Action ((x : (relativeWeight L) n) : (BRSTSpace L)) -
        ((((endpointBlocks L) hA n hp).comp a (a + shQm) ((0 : ℕ) : ℤ) ((0 : ℕ) : ℤ) x :
          (relativeWeight L) n) : (BRSTSpace L)) ∈ (NTp L) (a + shQm, ((0 : ℕ) : ℤ)) := by
  have hcomp : (((endpointBlocks L) hA n hp).comp a (a + shQm) ((0 : ℕ) : ℤ) ((0 : ℕ) : ℤ) x :
      (relativeWeight L) n) = ((endpointBlocks L) hA n hp).pr (a + shQm, ((0 : ℕ) : ℤ))
        ((relativeDifferential L) n (x : (relativeWeight L) n)) := by
    rw [KoszulBlocks.comp_coe, KoszulBlocks.pr_Qm_eq_pr_D _
      (((endpointBlocks L) hA n hp).le_deg _ _ x.2), ((endpointKahler L) hA).model_D n hp]
  rw [hcomp]
  have h := (pr_decomp L) hA hp (a + shQm, ((0 : ℕ) : ℤ)) ((relativeDifferential L) n (x : (relativeWeight L) n))
  rw [relativeDifferential_coe, brstComplex_Q] at h
  exact h

set_option maxHeartbeats 1000000 in
/-- **`π₁ ∘ d_CE = (grDiag L) ∘ π₀`.** -/
theorem π_intertwine (x : ((endpointBlocks L) hA n hp).blk (aR r, ((0 : ℕ) : ℤ))) (k : Fin 3 × ℕ) :
    (π1E L) hA hp r (((endpointBlocks L) hA n hp).comp (aR r) (aR r + shQm) ((0 : ℕ) : ℤ)
      ((0 : ℕ) : ℤ) x) k = (grDiag L) r k ((π0E L) hA hp r x) := by
  obtain ⟨c, kk⟩ := k
  obtain ⟨hx1, hx2⟩ := (blk_vacForm L) hA (n := n) (a := aR r) rfl (x : (relativeWeight L) n) x.2
  rw [π0E_apply, (grDiag_PiR_ev L) hA r c kk hx2]
  rcases Nat.eq_zero_or_pos kk with rfl | hkk
  · rw [π1E_apply, bAnB_zero_rel, map_zero, map_zero, map_zero, mPos_zero,
      (mMode_zero_of_rel L) c (x : (relativeWeight L) n) hx1, map_zero, map_zero]
  · have hh := (dCE_facts L) hA hp (aR r) x
    have hz1 := hh.1
    have hz2 := hh.2
    have e : semiInfiniteQ (matterAction L).toAffineSl2Action
        ((x : (relativeWeight L) n) : (BRSTSpace L)) =
        semiInfiniteQ (matterAction L).toAffineSl2Action
          ((extM L) ((x : (relativeWeight L) n) : (BRSTSpace L)) ⊗ₜ[ℂ] gvac) :=
      congrArg _ hx1
    rw [e] at hz2
    have h := (bAnB_dCE L) hA c hkk (a := aR r) (w := (n : ℂ)) hx2 hz1 hz2
    have h' := congrArg (fun v => (PiR L) hA r ((ev L) hA ((extM L) v))) h
    simp only [extM_tmul, vacφ_gvac, one_smul] at h'
    rw [π1E_apply']
    exact h'

end Inter

/-! ### Assembly -/

/-- **The symbol maps at the endpoint**, proved outright from `hA`. -/
def symbolResidual_endpoint : (EndpointSymbolResidual L) hA := fun _n hp r =>
  ⟨{ π0 := (π0E L) hA hp r
     ker_π0 := (ker_π0E L) hA hp r
     π1 := (π1E L) hA hp r
     ker_π1 := (ker_π1E L) hA hp r
     intertwine := (π_intertwine L) hA hp r }, (π0E_weight L) hA hp r⟩

/-- **The Koszul residual at the endpoint**, proved outright from `hA`. -/
def koszulResidual_endpoint : (EndpointKoszulResidual L) hA :=
  (koszulResidual_of_symbols L) hA ((symbolResidual_endpoint L) hA)


end

end VOA.TwoSeries
