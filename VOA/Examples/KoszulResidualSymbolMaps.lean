/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Examples.KoszulResidualSymbol

/-!
# The symbol maps `π₀`, `π₁` on the actual antighost-free blocks

At weight `n` and degree `r` (`a = (2r, 0)`):

* `π0E x = PiR (ev (extM x))` on the block `(a, 0)` — the vacuum coefficient of `x`, with its
  auxiliary `U`-symbol evaluated at `x = -a` and projected to `gr_r A ⊗ L_1`;
* `π1E y (c, k) = PiR (ev (extM (b^c_{(k)} y)))` on the block `(a + shQm, 0)`.

Proved: `ker π0E = range d_K`, `ker π1E = range d_K`, `π1E ∘ d_CE = grDiag ∘ π0E`, and `π0E`
lands in total weight `n`. Hence `symbolResidual_endpoint : EndpointSymbolResidual hA` and the
endpoint `leeYang_gradedUnitary_of_affine_strict`.

The symbol maps are proved outright from `hA`; the final theorem is additionally conditional on
`strict : ∀ r, GrJetStrict (r+1)` and `lower : LeeYangRRLowerBound` (both OPEN upstream).
-/

set_option linter.deprecated false

namespace VOA.KoszulResidual

open VOA.ConcreteHodge VOA.GradedUnitaryCohomology VOA.VertexOperatorAlgebra
open Sl2CosetConcrete Sl2SemiInfinite AffineSl2GeneralRigidity AffineSl2BelowCritical
open VOA.LeeYangTransferAssembly VOA.KoszulConcrete VOA.SympFerm VOA.Ghost
open VOA.SymbolModel VOA.CyclicEval AffineVOA
open scoped TensorProduct

noncomputable section

variable (hA : GradedUnitary affineForm affineRealStructure affineFlag)

/-- The bidegree `(2r, 0)`. -/
abbrev aR (r : ℕ) : ℤ × ℤ := (2 * (r : ℤ), 0)

/-- The block projection decomposes an ambient vector. -/
theorem pr_decomp {n : ℤ} (hp : IsPosOn ((endpointKahler hA).geometry n).P ⊤)
    (T : (ℤ × ℤ) × ℤ) (y : relativeWeight n) :
    (((endpointBlocks hA n hp).pr T y : relativeWeight n) : BRSTSpace) ∈ Tsup T ∧
      (y : BRSTSpace) - (((endpointBlocks hA n hp).pr T y : relativeWeight n) : BRSTSpace) ∈
        NTp T := by
  obtain ⟨p, hpdef⟩ : ∃ p, p = (endpointBlocks hA n hp).pr T y := ⟨_, rfl⟩
  rw [← hpdef]
  have hp1 : (p : BRSTSpace) ∈ blkSup n (· = T) := by
    rw [hpdef]; exact (endpointBlocks hA n hp).pr_mem T y
  refine ⟨?_, ?_⟩
  · exact (iSup_le fun j => iSup_le fun hj => le_iSup_of_le j (le_iSup_of_le hj.1 le_rfl) :
      blkSup n (· = T) ≤ Tsup T) hp1
  · have hyp : y - p ∈ ⨆ (b : (ℤ × ℤ) × ℤ) (_ : b ≠ T), blkE n b := by
      rw [hpdef]; exact KoszulBlocks.sub_pr_mem (endpointBlocks hA n hp) T y
    rw [← Submodule.coe_sub]
    refine Submodule.iSup_induction _ (motive := fun v : relativeWeight n => (v : BRSTSpace) ∈
      NTp T) hyp ?_ (by simp) (fun v w hv hw => by
        beta_reduce at hv hw ⊢; rw [Submodule.coe_add]; exact Submodule.add_mem _ hv hw)
    intro b v hv
    refine Submodule.iSup_induction _ (motive := fun v : relativeWeight n => (v : BRSTSpace) ∈
      NTp T) hv ?_ (by simp) (fun v w hv hw => by
        beta_reduce at hv hw ⊢; rw [Submodule.coe_add]; exact Submodule.add_mem _ hv hw)
    intro hb u hu
    have hu' : (u : BRSTSpace) ∈ blkSup n (· = b) := hu
    have hle : blkSup n (· = b) ≤ NTp T :=
      iSup_le fun j => iSup_le fun hj => le_iSup_of_le j (le_iSup_of_le
        (Or.inl (by rw [hj.1]; exact hb)) le_rfl)
    exact hle hu'

/-! ### `π₀` -/

section Pi0

variable {n : ℤ} (hp : IsPosOn ((endpointKahler hA).geometry n).P ⊤) (r : ℕ)

/-- **`π₀`**: evaluate the vacuum coefficient's auxiliary symbol at `x = -a`, project to
`gr_r A ⊗ L_1`. -/
def π0E : (endpointBlocks hA n hp).blk (aR r, ((0 : ℕ) : ℤ)) →ₗ[ℂ] GrA r ⊗[ℂ] BSpace :=
  PiR hA r ∘ₗ ev hA ∘ₗ extM ∘ₗ (relativeWeight n).subtype ∘ₗ
    ((endpointBlocks hA n hp).blk (aR r, ((0 : ℕ) : ℤ))).subtype

theorem π0E_apply (x : (endpointBlocks hA n hp).blk (aR r, ((0 : ℕ) : ℤ))) :
    π0E hA hp r x = PiR hA r (ev hA (extM ((x : relativeWeight n) : BRSTSpace))) := rfl

theorem π0E_eq_zero_iff (x : (endpointBlocks hA n hp).blk (aR r, ((0 : ℕ) : ℤ))) :
    π0E hA hp r x = 0 ↔ EVB hA ((x : relativeWeight n) : BRSTSpace) = 0 := by
  obtain ⟨hx1, hx2⟩ := blk_vacForm hA (n := n) (a := aR r) rfl (x : relativeWeight n) x.2
  rw [π0E_apply]
  conv_rhs => rw [hx1, EVB_tmul_gvac]
  constructor
  · intro h
    rw [PiR_injOn hA r (ev_mem hA _ _ hx2) h, TensorProduct.zero_tmul]
  · intro h
    rw [eq_zero_of_tmul_gvac h, map_zero]

theorem ker_π0E :
    LinearMap.ker (π0E hA hp r) = LinearMap.range ((endpointBlocks hA n hp).comp
      (aR r - shQm) (aR r) ((0 + 1 : ℕ) : ℤ) ((0 : ℕ) : ℤ)) := by
  ext x
  rw [LinearMap.mem_ker, range_comp_iff hA hp (by abel) x, π0E_eq_zero_iff]

theorem π0E_weight (x : (endpointBlocks hA n hp).blk (aR r, ((0 : ℕ) : ℤ))) :
    π0E hA hp r x ∈ tensorWeight (grDeg r) bWeight n := by
  obtain ⟨-, hx2⟩ := blk_vacForm hA (n := n) (a := aR r) rfl (x : relativeWeight n) x.2
  exact PiR_weight hA r n (ev_mem hA _ _ hx2)

end Pi0

/-! ### `π₁` -/

section Pi1

variable {n : ℤ} (hp : IsPosOn ((endpointKahler hA).geometry n).P ⊤) (r : ℕ)

/-- **`π₁`**: the `c^c_{-k}`-coefficient, evaluated as for `π₀`. -/
def π1E : (endpointBlocks hA n hp).blk (aR r + shQm, ((0 : ℕ) : ℤ)) →ₗ[ℂ]
    (Fin 3 × ℕ → GrA r ⊗[ℂ] BSpace) :=
  LinearMap.pi fun k => PiR hA r ∘ₗ ev hA ∘ₗ extM ∘ₗ
    TensorProduct.map LinearMap.id (bAn k.1 k.2) ∘ₗ (relativeWeight n).subtype ∘ₗ
      ((endpointBlocks hA n hp).blk (aR r + shQm, ((0 : ℕ) : ℤ))).subtype

theorem π1E_apply (y : (endpointBlocks hA n hp).blk (aR r + shQm, ((0 : ℕ) : ℤ)))
    (k : Fin 3 × ℕ) :
    π1E hA hp r y k = PiR hA r (ev hA (extM (TensorProduct.map LinearMap.id (bAn k.1 k.2)
      ((y : relativeWeight n) : BRSTSpace)))) := rfl

theorem π1E_apply' (y : (endpointBlocks hA n hp).blk (aR r + shQm, ((0 : ℕ) : ℤ)))
    (c : Fin 3) (kk : ℕ) :
    π1E hA hp r y (c, kk) = PiR hA r (ev hA (extM (TensorProduct.map LinearMap.id (bAn c kk)
      ((y : relativeWeight n) : BRSTSpace)))) := rfl

theorem EVB_mapG (G : Module.End ℂ Sl2GhostSpace) (v : BRSTSpace) :
    EVB hA (TensorProduct.map LinearMap.id G v) = TensorProduct.map LinearMap.id G (EVB hA v) := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul m g => simp [EVB]

theorem map_NT_eq (T : Finset (Fin 3 × (ℕ × Fin 2))) (v : (ASpace ⊗[ℂ] BSpace) ⊗[ℂ] Sl2GhostSpace) :
    TensorProduct.map LinearMap.id (NT T) v = ∑ t ∈ T, TensorProduct.map LinearMap.id
      (ConcreteHodge.Cr t.1 t.2) (TensorProduct.map LinearMap.id (ConcreteHodge.An t.1 t.2) v) := by
  rw [NT, map_id_sum, LinearMap.coe_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [← LinearMap.comp_apply, ← TensorProduct.map_comp, LinearMap.id_comp]

theorem π1E_eq_zero_iff (y : (endpointBlocks hA n hp).blk (aR r + shQm, ((0 : ℕ) : ℤ))) :
    π1E hA hp r y = 0 ↔ EVB hA ((y : relativeWeight n) : BRSTSpace) = 0 := by
  obtain ⟨hy1, hy2⟩ := blk_oneC hA (n := n) (a := aR r + shQm) (by simp [shQm])
    (y : relativeWeight n) y.2
  constructor
  · intro h
    have hk : ∀ (c : Fin 3) (kk : ℕ), EVB hA (TensorProduct.map LinearMap.id (bAn c kk)
        ((y : relativeWeight n) : BRSTSpace)) = 0 := by
      intro c kk
      rcases Nat.eq_zero_or_pos kk with rfl | hkk
      · rw [bAnB_zero_rel, map_zero]
      · obtain ⟨hP, hD⟩ := hy2 c kk hkk
        have h0 := congrFun h (c, kk)
        rw [π1E_apply, Pi.zero_apply] at h0
        have hD' : extM (TensorProduct.map LinearMap.id (bAn c kk)
            ((y : relativeWeight n) : BRSTSpace)) ∈ matterDeg ((aR r, ((n - kk : ℤ) : ℂ))) := by
          convert hD using 2
          simp [aR, shQm]
        have hev := PiR_injOn hA r (ev_mem hA _ _ hD') h0
        rw [← hP, map_Pvac_eq, EVB_tmul_gvac, hev, TensorProduct.zero_tmul]
    rw [← hy1, EVB_mapG, map_NT_eq]
    refine Finset.sum_eq_zero fun t ht => ?_
    obtain ⟨c, kk, e⟩ := t
    have he : e = 1 := (mem_Tc.mp ht).2
    subst he
    rw [← EVB_mapG]
    change TensorProduct.map LinearMap.id (ConcreteHodge.Cr c (kk, 1))
      (EVB hA (TensorProduct.map LinearMap.id (bAn c kk) ((y : relativeWeight n) : BRSTSpace))) = 0
    rw [hk c kk, map_zero]
  · intro h
    funext k
    have h0 : EVB hA (TensorProduct.map LinearMap.id (bAn k.1 k.2)
        ((y : relativeWeight n) : BRSTSpace)) = 0 := by
      rw [EVB_mapG, h, map_zero]
    show π1E hA hp r y k = 0
    rw [π1E_apply, ev_extM_eq_ext, h0, map_zero, map_zero, map_zero]

theorem ker_π1E :
    LinearMap.ker (π1E hA hp r) = LinearMap.range ((endpointBlocks hA n hp).comp
      (aR r) (aR r + shQm) ((0 + 1 : ℕ) : ℤ) ((0 : ℕ) : ℤ)) := by
  ext y
  rw [LinearMap.mem_ker, range_comp_iff hA hp rfl y, π1E_eq_zero_iff]

end Pi1

/-! ### The intertwining -/

section Inter

variable {n : ℤ} (hp : IsPosOn ((endpointKahler hA).geometry n).P ⊤) (r : ℕ)

theorem grDiag_PiR_ev (c : Fin 3) (kk : ℕ) {m : MatterSpace} (hm : m ∈ matterDeg (aR r, (n : ℂ))) :
    grDiag r (c, kk) (PiR hA r (ev hA m)) = PiR hA r (ev hA (mPos hA c kk m)) := by
  have hev := ev_mem hA _ m hm
  rw [ev_mPos, map_add, PiR_aPos hA r c kk hev, PiR_bMode, grDiag, LinearMap.add_apply]

theorem mMode_zero_of_rel (c : Fin 3) (x : relativeWeight n) {m : MatterSpace}
    (hx : (x : BRSTSpace) = m ⊗ₜ[ℂ] gvac) : mMode c 0 m = 0 := by
  have h := ((mem_relativeCarrier _ _).mp x.2.1).1 c
  rw [hx, totalZero_tmul', show Jz c gvac = 0 from Jz_vacuum c, TensorProduct.tmul_zero,
    add_zero] at h
  exact eq_zero_of_tmul_gvac' h

set_option maxHeartbeats 1000000 in
/-- The `d_CE` component is the `(a + shQm, 0)` block projection of `Q x`. -/
theorem dCE_facts (a : ℤ × ℤ) (x : (endpointBlocks hA n hp).blk (a, ((0 : ℕ) : ℤ))) :
    (((endpointBlocks hA n hp).comp a (a + shQm) ((0 : ℕ) : ℤ) ((0 : ℕ) : ℤ) x :
        relativeWeight n) : BRSTSpace) ∈ Tsup (a + shQm, ((0 : ℕ) : ℤ)) ∧
      semiInfiniteQ leeYangMatterAction.toAffineSl2Action ((x : relativeWeight n) : BRSTSpace) -
        (((endpointBlocks hA n hp).comp a (a + shQm) ((0 : ℕ) : ℤ) ((0 : ℕ) : ℤ) x :
          relativeWeight n) : BRSTSpace) ∈ NTp (a + shQm, ((0 : ℕ) : ℤ)) := by
  have hcomp : ((endpointBlocks hA n hp).comp a (a + shQm) ((0 : ℕ) : ℤ) ((0 : ℕ) : ℤ) x :
      relativeWeight n) = (endpointBlocks hA n hp).pr (a + shQm, ((0 : ℕ) : ℤ))
        (relativeDifferential n (x : relativeWeight n)) := by
    rw [KoszulBlocks.comp_coe, KoszulBlocks.pr_Qm_eq_pr_D _
      ((endpointBlocks hA n hp).le_deg _ _ x.2), (endpointKahler hA).model_D n hp]
  rw [hcomp]
  have h := pr_decomp hA hp (a + shQm, ((0 : ℕ) : ℤ)) (relativeDifferential n (x : relativeWeight n))
  rw [relativeDifferential_coe, leeYangBRSTComplex_Q] at h
  exact h

set_option maxHeartbeats 1000000 in
/-- **`π₁ ∘ d_CE = grDiag ∘ π₀`.** -/
theorem π_intertwine (x : (endpointBlocks hA n hp).blk (aR r, ((0 : ℕ) : ℤ))) (k : Fin 3 × ℕ) :
    π1E hA hp r ((endpointBlocks hA n hp).comp (aR r) (aR r + shQm) ((0 : ℕ) : ℤ)
      ((0 : ℕ) : ℤ) x) k = grDiag r k (π0E hA hp r x) := by
  obtain ⟨c, kk⟩ := k
  obtain ⟨hx1, hx2⟩ := blk_vacForm hA (n := n) (a := aR r) rfl (x : relativeWeight n) x.2
  rw [π0E_apply, grDiag_PiR_ev hA r c kk hx2]
  rcases Nat.eq_zero_or_pos kk with rfl | hkk
  · rw [π1E_apply, bAnB_zero_rel, map_zero, map_zero, map_zero, mPos_zero,
      mMode_zero_of_rel c (x : relativeWeight n) hx1, map_zero, map_zero]
  · have hh := dCE_facts hA hp (aR r) x
    have hz1 := hh.1
    have hz2 := hh.2
    have e : semiInfiniteQ leeYangMatterAction.toAffineSl2Action
        ((x : relativeWeight n) : BRSTSpace) =
        semiInfiniteQ leeYangMatterAction.toAffineSl2Action
          (extM ((x : relativeWeight n) : BRSTSpace) ⊗ₜ[ℂ] gvac) :=
      congrArg _ hx1
    rw [e] at hz2
    have h := bAnB_dCE hA c hkk (a := aR r) (w := (n : ℂ)) hx2 hz1 hz2
    have h' := congrArg (fun v => PiR hA r (ev hA (extM v))) h
    simp only [extM_tmul, vacφ_gvac, one_smul] at h'
    rw [π1E_apply']
    exact h'

end Inter

/-! ### Assembly -/

/-- **The symbol maps at the endpoint**, proved outright from `hA`. -/
def symbolResidual_endpoint : EndpointSymbolResidual hA := fun _n hp r =>
  ⟨{ π0 := π0E hA hp r
     ker_π0 := ker_π0E hA hp r
     π1 := π1E hA hp r
     ker_π1 := ker_π1E hA hp r
     intertwine := π_intertwine hA hp r }, π0E_weight hA hp r⟩

/-- **The Koszul residual at the endpoint**, proved outright from `hA`. -/
def koszulResidual_endpoint : EndpointKoszulResidual hA :=
  koszulResidual_of_symbols hA (symbolResidual_endpoint hA)

/-- **Graded unitarity of Lee–Yang from graded unitarity of `L_{-4/3}(sl₂)`**, conditional
only on the strict jet inequalities and the Rogers–Ramanujan lower bound. -/
theorem leeYang_gradedUnitary_of_affine_strict
    (hA : GradedUnitary affineForm affineRealStructure affineFlag)
    (strict : ∀ r : ℕ, GrJetStrict (r + 1))
    (lower : LeeYangCharacter.LeeYangRRLowerBound) :
    VirGradedUnitarity.VirGradedUnitary LeeYang.leeYangC leeYangRealStructure :=
  leeYang_gradedUnitary_of_affine_symbolResidual hA strict (symbolResidual_endpoint hA) lower

end

end VOA.KoszulResidual
