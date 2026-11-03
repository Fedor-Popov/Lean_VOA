/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Examples.KoszulResidualHomotopy

/-!
# Koszul exactness of the actual `d_K` on the endpoint blocks

For the antighost-count blocks `B = endpointBlocks hA n hp` of the actual relative complex:

* `blk_mem_goodSup` — a block vector lies in the `c₀`-free joint pieces of its block;
* `pr_eq_of_decomp` — the block projection is computed by any ambient decomposition into the
  target block and complementary joint pieces;
* `comp_coe_eq_dN` — **the actual block component `d_K` of `Q⁻` is the native Koszul
  differential `dN (sN N)`**, `N = n.toNat`;
* `hN_mem_blk` — the native homotopy `hN (sN N)` maps blocks to blocks (relative states to
  relative states);
* `kExactAt_endpoint`, `kExact_endpoint` — **Koszul exactness** `KoszulBlocks.KExact` of the
  actual blocks, at every bidegree.

Everything is proved outright from `hA`.
-/

namespace VOA.KoszulResidual

open VOA.ConcreteHodge VOA.GradedUnitaryCohomology VOA.VertexOperatorAlgebra
open Sl2CosetConcrete Sl2SemiInfinite AffineSl2GeneralRigidity AffineSl2BelowCritical
open VOA.LeeYangTransferAssembly VOA.KoszulConcrete VOA.SympFerm VOA.Ghost
open scoped TensorProduct

noncomputable section

variable (hA : GradedUnitary affineForm affineRealStructure affineFlag)

/-- The internal joint grading used by the endpoint blocks. -/
abbrev hIB : DirectSum.IsInternal KoszulConcrete.blockB :=
  blockB_isInternal hA LevelOneUnitary.bUnitary unitWeight unitWeight_pos

/-! ### Antighost anticommutation and relative states -/

theorem antighostZero_hN (N : ℕ) (a : Fin 3) (v : BRSTSpace) :
    antighostZero matterSVA a (hN (sN N) v) = -hN (sN N) (antighostZero matterSVA a v) := by
  rw [antighostZero_eq]
  induction v using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy, neg_add]
  | tmul m g =>
      simp only [hN, LinearMap.coe_sum, Finset.sum_apply, map_sum, TensorProduct.map_tmul,
        LinearMap.id_apply, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [← TensorProduct.tmul_neg]
      congr 1
      exact An_Cr_ne (a := a) (q := (0, 1)) (by rintro ⟨-, h⟩; simp at h) g

theorem hN_mem_relativeCarrier (N : ℕ) {v : BRSTSpace}
    (hv : v ∈ relativeCarrier leeYangMatterAction.toAffineSl2Action) :
    hN (sN N) v ∈ relativeCarrier leeYangMatterAction.toAffineSl2Action := by
  rw [mem_relativeCarrier] at hv ⊢
  refine ⟨fun a => ?_, fun a => ?_⟩
  · rw [totalZero_hN, hv.1 a, map_zero]
  · rw [antighostZero_hN, hv.2 a, map_zero, neg_zero]

/-! ### Block vectors in joint pieces -/

/-- The `c₀`-free joint pieces of a block. -/
def goodSup (n : ℤ) (b : (ℤ × ℤ) × ℤ) : Submodule ℂ BRSTSpace :=
  ⨆ (j : KF × ℤ) (_ : bIdx j = b ∧ wIdx j = (n : ℂ) ∧ j.1.2 = 0), KoszulConcrete.blockB j

theorem iproj_eq_zero_of_c0 {x : BRSTSpace} (hx : x ∈ ⨆ (k : KF) (_ : k.2 = 0), brstDegF k)
    {j : KF × ℤ} (hj : j.1.2 ≠ 0) : iproj (hIB hA) j x = 0 := by
  refine Submodule.iSup_induction _ (motive := fun x => iproj (hIB hA) j x = 0) hx ?_
    (map_zero _) (fun x y hx hy => by beta_reduce at hx hy ⊢; rw [map_add, hx, hy, add_zero])
  intro k y hy
  refine Submodule.iSup_induction _ (motive := fun x => iproj (hIB hA) j x = 0) hy ?_
    (map_zero _) (fun x y hx hy => by beta_reduce at hx hy ⊢; rw [map_add, hx, hy, add_zero])
  intro hk z hz
  exact iproj_eq_zero_of_weight (hIB hA)
    (brstDegF_isInternal hA LevelOneUnitary.bUnitary unitWeight unitWeight_pos)
    (fun j : KF × ℤ => j.1) blockB_le_brstDegF hz (fun e => hj (by simp only at e; rw [e]; exact hk))

include hA in
/-- **A block vector lies in the `c₀`-free joint pieces of its block.** -/
theorem blk_mem_goodSup {n : ℤ} {b : (ℤ × ℤ) × ℤ} (x : relativeWeight n) (hx : x ∈ blkE n b) :
    (x : BRSTSpace) ∈ goodSup n b := by
  refine mem_iSup_of_iproj (hIB hA) _ fun j hj => ?_
  by_cases h1 : bIdx j = b ∧ wIdx j = (n : ℂ)
  · have hc := relative_c0free hA LevelOneUnitary.bUnitary unitWeight unitWeight_pos
      (z := (x : BRSTSpace)) (fun a => ((mem_relativeCarrier _ _).mp x.2.1).2 a)
    exact iproj_eq_zero_of_c0 hA hc (fun h => hj ⟨h1.1, h1.2, h⟩)
  · have hx' : (x : BRSTSpace) ∈ blkSup n (· = b) := hx
    refine iproj_blkSup_eq_zero n hA LevelOneUnitary.bUnitary unitWeight unitWeight_pos hx' ?_
    by_cases h2 : bIdx j = b
    · exact Or.inr fun h => h1 ⟨h2, h⟩
    · exact Or.inl h2

/-! ### The block projection through an ambient decomposition -/

/-- Generic: a vector minus its block component lies in the other blocks. -/
theorem KoszulBlocks.sub_pr_mem {K : Type*} [AddCommGroup K] [Module ℂ K] {C : KahlerComplex K}
    (B : KoszulBlocks C) (T : (ℤ × ℤ) × ℤ) (y : K) :
    y - B.pr T y ∈ ⨆ (b : (ℤ × ℤ) × ℤ) (_ : b ≠ T), B.blk b := by
  refine mem_iSup_of_iproj B.internal (· ≠ T) fun b hb => ?_
  push Not at hb
  subst hb
  change B.pr b (y - B.pr b y) = 0
  rw [map_sub, B.pr_of_mem (B.pr_mem b y), sub_self]

/-- The joint pieces outside a block index (or with negative `c₀`). -/
def NTp (T : (ℤ × ℤ) × ℤ) : Submodule ℂ BRSTSpace :=
  ⨆ (j' : KF × ℤ) (_ : bIdx j' ≠ T ∨ j'.1.2 < 0), KoszulConcrete.blockB j'

theorem NTsup_eq (j : KF × ℤ) : NTsup j = NTp (bIdx (j + δT)) := rfl

/-- **The block projection through an ambient decomposition.** -/
theorem pr_coe_eq {n : ℤ} (hp : IsPosOn ((endpointKahler hA).geometry n).P ⊤)
    (T : (ℤ × ℤ) × ℤ) (y : relativeWeight n) {z' : BRSTSpace} (hz' : z' ∈ blkSup n (· = T))
    (hyz : (y : BRSTSpace) - z' ∈ NTp T) :
    (((endpointBlocks hA n hp).pr T y : relativeWeight n) : BRSTSpace) = z' := by
  obtain ⟨p, hpdef⟩ : ∃ p, p = (endpointBlocks hA n hp).pr T y := ⟨_, rfl⟩
  rw [← hpdef]
  have hp1 : (p : BRSTSpace) ∈ blkSup n (· = T) := by
    rw [hpdef]; exact (endpointBlocks hA n hp).pr_mem T y
  -- `y - p` lies in the other blocks
  have hyp : y - p ∈ ⨆ (b : (ℤ × ℤ) × ℤ) (_ : b ≠ T), blkE n b := by
    rw [hpdef]; exact KoszulBlocks.sub_pr_mem (endpointBlocks hA n hp) T y
  have hyp' : ((y - p : relativeWeight n) : BRSTSpace) ∈
      ⨆ (j : KF × ℤ) (_ : bIdx j ≠ T), KoszulConcrete.blockB j := by
    refine Submodule.iSup_induction _ (motive := fun v : relativeWeight n => (v : BRSTSpace) ∈
      ⨆ (j : KF × ℤ) (_ : bIdx j ≠ T), KoszulConcrete.blockB j) hyp ?_
      (by simp) (fun v w hv hw => by
        beta_reduce at hv hw ⊢; rw [Submodule.coe_add]; exact Submodule.add_mem _ hv hw)
    intro b v hv
    refine Submodule.iSup_induction _ (motive := fun v : relativeWeight n => (v : BRSTSpace) ∈
      ⨆ (j : KF × ℤ) (_ : bIdx j ≠ T), KoszulConcrete.blockB j) hv ?_
      (by simp) (fun v w hv hw => by
        beta_reduce at hv hw ⊢; rw [Submodule.coe_add]; exact Submodule.add_mem _ hv hw)
    intro hb u hu
    have hu' : (u : BRSTSpace) ∈ blkSup n (· = b) := hu
    have hle : blkSup n (· = b) ≤ ⨆ (j : KF × ℤ) (_ : bIdx j ≠ T), KoszulConcrete.blockB j :=
      iSup_le fun j => iSup_le fun hj => le_iSup_of_le j (le_iSup_of_le (by rw [hj.1]; exact hb)
        le_rfl)
    exact hle hu'
  refine eq_of_iproj_eq (hIB hA) fun j' => ?_
  by_cases hj' : bIdx j' = T
  · by_cases hc : j'.1.2 < 0
    · have h1 := iproj_mem (hIB hA) j' (p : BRSTSpace)
      have h2 := iproj_mem (hIB hA) j' z'
      rw [blockB_eq_bot_of_c0 (by omega), Submodule.mem_bot] at h1 h2
      rw [h1, h2]
    · have e1 : iproj (hIB hA) j' ((y : BRSTSpace) - z') = 0 :=
        iproj_eq_zero_of_mem_iSup (hIB hA) _ hyz (by
          rintro (h | h)
          · exact h hj'
          · exact hc h)
      have e2 : iproj (hIB hA) j' (((y - p : relativeWeight n) : BRSTSpace)) = 0 :=
        iproj_eq_zero_of_mem_iSup (hIB hA) _ hyp' (fun h => h hj')
      rw [map_sub, sub_eq_zero] at e1
      rw [Submodule.coe_sub, map_sub, sub_eq_zero] at e2
      rw [← e2, e1]
  · rw [iproj_blkSup_eq_zero n hA LevelOneUnitary.bUnitary unitWeight unitWeight_pos hp1
      (Or.inl hj'), iproj_blkSup_eq_zero n hA LevelOneUnitary.bUnitary unitWeight unitWeight_pos
      hz' (Or.inl hj')]

/-! ### The actual `d_K` is the native Koszul differential -/

theorem goodSup_induction {n : ℤ} {b : (ℤ × ℤ) × ℤ} (Φ : BRSTSpace → Prop) (h0 : Φ 0)
    (hadd : ∀ x y, Φ x → Φ y → Φ (x + y))
    (hj : ∀ j : KF × ℤ, bIdx j = b → wIdx j = (n : ℂ) → j.1.2 = 0 →
      ∀ z ∈ KoszulConcrete.blockB j, Φ z) :
    ∀ x ∈ goodSup n b, Φ x := by
  intro x hx
  refine Submodule.iSup_induction _ (motive := Φ) hx ?_ h0 hadd
  intro j y hy
  refine Submodule.iSup_induction _ (motive := Φ) hy ?_ h0 hadd
  intro hj' z hz
  exact hj j hj'.1 hj'.2.1 hj'.2.2 z hz

theorem bIdx_add_δT (j : KF × ℤ) : bIdx (j + δT) = (j.1.1.1 + shQm, j.2 - 1) := by
  simp [bIdx, shQm, sub_eq_add_neg]

theorem bIdx_add_δH (j : KF × ℤ) : bIdx (j + δH) = (j.1.1.1 - shQm, j.2 + 1) := by
  simp [bIdx, shQm, sub_eq_add_neg]

theorem wIdx_add_δT (j : KF × ℤ) : wIdx (j + δT) = wIdx j := by simp [wIdx]

theorem wIdx_add_δH (j : KF × ℤ) : wIdx (j + δH) = wIdx j := by simp [wIdx]

theorem le_toNat (n : ℤ) : n ≤ (n.toNat : ℤ) := Int.self_le_toNat n

/-- `Q - dN` and `dN` on a good block vector. -/
theorem Q_dN_goodSup {n : ℤ} {a : ℤ × ℤ} {q : ℤ} {x : BRSTSpace} (hx : x ∈ goodSup n (a, q)) :
    semiInfiniteQ leeYangMatterAction.toAffineSl2Action x - dN hA (sN n.toNat) x ∈
        NTp (a + shQm, q - 1) ∧
      dN hA (sN n.toNat) x ∈ blkSup n (· = (a + shQm, q - 1)) := by
  refine goodSup_induction (fun x => semiInfiniteQ leeYangMatterAction.toAffineSl2Action x -
      dN hA (sN n.toNat) x ∈ NTp (a + shQm, q - 1) ∧
      dN hA (sN n.toNat) x ∈ blkSup n (· = (a + shQm, q - 1))) (by simp)
    (fun x y hx hy => ⟨by rw [map_add, map_add, add_sub_add_comm]; exact Submodule.add_mem _ hx.1 hy.1,
      by rw [map_add]; exact Submodule.add_mem _ hx.2 hy.2⟩) ?_ x hx
  intro j hb hw hc z hz
  have hT : bIdx (j + δT) = (a + shQm, q - 1) := by
    rw [bIdx_add_δT]
    have h1 : j.1.1.1 = a := congrArg Prod.fst hb
    have h2 : j.2 = q := congrArg Prod.snd hb
    rw [h1, h2]
  refine ⟨?_, ?_⟩
  · have h := Q_sub_dN_mem hA n.toNat hc (n0 := n) hw (le_toNat n) z hz
    rwa [NTsup_eq, hT] at h
  · exact Submodule.mem_iSup_of_mem (j + δT) (Submodule.mem_iSup_of_mem
      ⟨hT, by rw [wIdx_add_δT]; exact hw⟩ (dN_mem_blockB hA _ j z hz))

/-- **The actual block component `d_K` of `Q⁻` is the native Koszul differential.** -/
theorem comp_coe_eq_dN {n : ℤ} (hp : IsPosOn ((endpointKahler hA).geometry n).P ⊤)
    (a : ℤ × ℤ) {q q' : ℤ} (hq : q' + 1 = q)
    (x : (endpointBlocks hA n hp).blk (a, q)) :
    ((((endpointBlocks hA n hp).comp a (a + shQm) q q' x : relativeWeight n)) : BRSTSpace) =
      dN hA (sN n.toNat) ((x : relativeWeight n) : BRSTSpace) := by
  have hq' : q' = q - 1 := by omega
  subst hq'
  rw [KoszulBlocks.comp_coe, KoszulBlocks.pr_Qm_eq_pr_D _ ((endpointBlocks hA n hp).le_deg a q x.2),
    (endpointKahler hA).model_D n hp]
  have hgood := blk_mem_goodSup hA (x : relativeWeight n) x.2
  obtain ⟨h1, h2⟩ := Q_dN_goodSup hA hgood
  refine pr_coe_eq hA hp _ _ h2 ?_
  rw [relativeDifferential_coe, leeYangBRSTComplex_Q]
  exact h1

/-! ### The homotopy preserves blocks -/

theorem blkSup_le_grading (n : ℤ) (S : (ℤ × ℤ) × ℤ → Prop) :
    blkSup n S ≤ brstSVA.grading (n : ℂ) :=
  iSup_le fun j => iSup_le fun hj => by
    have h := blockB_le_weight unitWeight j
    rw [show j.1.1.2 = (n : ℂ) from hj.2] at h
    exact h

/-- **`hN` maps a block vector to the block below.** -/
theorem hN_goodSup {n : ℤ} {a b : ℤ × ℤ} (hb : b + shQm = a) {q : ℤ} {x : BRSTSpace}
    (hx : x ∈ goodSup n (a, q)) (N : ℕ) : hN (sN N) x ∈ blkSup n (· = (b, q + 1)) := by
  refine goodSup_induction (fun x => hN (sN N) x ∈ blkSup n (· = (b, q + 1))) (by simp)
    (fun x y hx hy => by beta_reduce at hx hy ⊢; rw [map_add]; exact Submodule.add_mem _ hx hy)
    ?_ x hx
  intro j hbj hw hc z hz
  have hT : bIdx (j + δH) = (b, q + 1) := by
    rw [bIdx_add_δH]
    have h1 : j.1.1.1 = a := congrArg Prod.fst hbj
    have h2 : j.2 = q := congrArg Prod.snd hbj
    rw [h1, h2, ← hb, add_sub_cancel_right]
  exact Submodule.mem_iSup_of_mem (j + δH) (Submodule.mem_iSup_of_mem
    ⟨hT, by rw [wIdx_add_δH]; exact hw⟩ (hN_mem_blockB _ j z hz))

include hA in
theorem hN_mem_relativeWeight {n : ℤ} {a b : ℤ × ℤ} (hb : b + shQm = a) {q : ℤ}
    (x : relativeWeight n) (hx : x ∈ blkE n (a, q)) (N : ℕ) :
    hN (sN N) (x : BRSTSpace) ∈ relativeWeight n := by
  have hs := hN_goodSup hb (blk_mem_goodSup hA x hx) N
  exact ⟨hN_mem_relativeCarrier N x.2.1, blkSup_le_grading n _ hs⟩

/-! ### Injectivity of the Koszul Laplacian -/

/-- The joint pieces of antighost number `q₀` and integral weight `≤ N`. -/
def lapSup (N : ℕ) (q0 : ℤ) : Submodule ℂ BRSTSpace :=
  ⨆ (j : KF × ℤ) (_ : j.2 = q0 ∧ ∃ n0 : ℤ, n0 ≤ N ∧ j.1.1.2 = (n0 : ℂ)), KoszulConcrete.blockB j

theorem NbB_lapSup (N : ℕ) (q0 : ℤ) {v : BRSTSpace} (hv : v ∈ lapSup N q0) :
    TensorProduct.map LinearMap.id (Nb (sN N)) v = (q0 : ℂ) • v := by
  refine Submodule.iSup_induction _ (motive := fun v =>
    TensorProduct.map LinearMap.id (Nb (sN N)) v = (q0 : ℂ) • v) hv ?_ (by simp)
    (fun x y hx hy => by beta_reduce at hx hy ⊢; rw [map_add, hx, hy, smul_add])
  intro j y hy
  refine Submodule.iSup_induction _ (motive := fun v =>
    TensorProduct.map LinearMap.id (Nb (sN N)) v = (q0 : ℂ) • v) hy ?_ (by simp)
    (fun x y hx hy => by beta_reduce at hx hy ⊢; rw [map_add, hx, hy, smul_add])
  intro hj z hz
  obtain ⟨hq, n0, hn0, hw⟩ := hj
  rw [NbB_blockB N hw hn0 z hz, hq]

theorem rTensor_injective_ghost {f : Module.End ℂ MatterSpace} (hf : Function.Injective f) :
    Function.Injective (TensorProduct.map f (LinearMap.id : Module.End ℂ Sl2GhostSpace)) := by
  have h := Module.Flat.rTensor_preserves_injective_linearMap (R := ℂ) (M := Sl2GhostSpace) f hf
  exact h

/-- **`ΔN + c` is injective on joint pieces of antighost number `q₀` with `q₀ + c ≥ 1`.** -/
theorem ΔN_add_injective (N : ℕ) {q0 : ℤ} {c : ℕ} (hc : 1 ≤ q0 + c) {v : BRSTSpace}
    (hv : v ∈ lapSup N q0) (h : ΔN hA (sN N) v + (c : ℂ) • v = 0) : v = 0 := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (k : ℤ) = q0 + c := ⟨(q0 + c).toNat, by omega⟩
  have hk1 : 1 ≤ k := by omega
  have hf : Function.Injective (mL hA (sN N) + (k : ℂ) •
      (LinearMap.id : Module.End ℂ MatterSpace)) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    exact mL_add_injective hA (sN N) hk1 (by simpa using hw)
  apply rTensor_injective_ghost hf
  rw [map_zero, ← h, ΔN, LinearMap.add_apply, NbB_lapSup N q0 hv]
  rw [show TensorProduct.map (mL hA (sN N) + (k : ℂ) • (LinearMap.id : Module.End ℂ MatterSpace))
      (LinearMap.id : Module.End ℂ Sl2GhostSpace) = TensorProduct.map (mL hA (sN N))
      (LinearMap.id : Module.End ℂ Sl2GhostSpace) + (k : ℂ) •
        (LinearMap.id : Module.End ℂ BRSTSpace) by
    rw [TensorProduct.map_add_left, TensorProduct.map_smul_left, TensorProduct.map_id]]
  rw [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply, add_assoc, ← add_smul]
  have hkc : (k : ℂ) = (q0 : ℂ) + (c : ℂ) := by exact_mod_cast hk
  rw [hkc]

theorem goodSup_le_lapSup {n : ℤ} {a : ℤ × ℤ} {q : ℤ} :
    goodSup n (a, q) ≤ lapSup n.toNat q :=
  iSup_le fun j => iSup_le fun hj => le_iSup_of_le j (le_iSup_of_le
    ⟨congrArg Prod.snd hj.1, n, le_toNat n, hj.2.1⟩ le_rfl)

theorem mDerB_lapSup (N : ℕ) (q0 : ℤ) (qq : LexLetter) {v : BRSTSpace} (hv : v ∈ lapSup N q0) :
    mDerB qq v ∈ lapSup N q0 := by
  refine Submodule.iSup_induction _ (motive := fun v => mDerB qq v ∈ lapSup N q0) hv ?_
    (by simp) (fun x y hx hy => by beta_reduce at hx hy ⊢; rw [map_add]; exact Submodule.add_mem _ hx hy)
  intro j y hy
  refine Submodule.iSup_induction _ (motive := fun v => mDerB qq v ∈ lapSup N q0) hy ?_
    (by simp) (fun x y hx hy => by beta_reduce at hx hy ⊢; rw [map_add]; exact Submodule.add_mem _ hx hy)
  intro hj z hz
  obtain ⟨hq, n0, hn0, hw⟩ := hj
  refine Submodule.mem_iSup_of_mem (j + ((-(eq qq), 0), 0)) (Submodule.mem_iSup_of_mem
    ⟨by simp [hq], n0 - letterWt qq, by omega, ?_⟩ (mDerB_mem_blockB qq j z hz))
  simp only [Prod.fst_add, Prod.snd_add, Prod.snd_neg, hw, eq, letterWt]
  push_cast; ring

/-! ### Koszul exactness -/

theorem comp_coe_eq_dN' {n : ℤ} (hp : IsPosOn ((endpointKahler hA).geometry n).P ⊤)
    {a c : ℤ × ℤ} (hc : a + shQm = c) {q q' : ℤ} (hq : q' + 1 = q)
    (x : (endpointBlocks hA n hp).blk (a, q)) :
    ((((endpointBlocks hA n hp).comp a c q q' x : relativeWeight n)) : BRSTSpace) =
      dN hA (sN n.toNat) ((x : relativeWeight n) : BRSTSpace) := by
  subst hc
  exact comp_coe_eq_dN hA hp a hq x

/-- The ambient image of a block. -/
abbrev blkW (n : ℤ) (hp : IsPosOn ((endpointKahler hA).geometry n).P ⊤) (i : (ℤ × ℤ) × ℤ) :
    Submodule ℂ BRSTSpace :=
  ((endpointBlocks hA n hp).blk i).map (relativeWeight n).subtype

theorem blkW_le_goodSup {n : ℤ} (hp : IsPosOn ((endpointKahler hA).geometry n).P ⊤)
    (i : (ℤ × ℤ) × ℤ) : blkW hA n hp i ≤ goodSup n i := by
  rintro _ ⟨v, hv, rfl⟩
  exact blk_mem_goodSup hA v hv

theorem mem_blkW_of {n : ℤ} (hp : IsPosOn ((endpointKahler hA).geometry n).P ⊤)
    {i : (ℤ × ℤ) × ℤ} {v : BRSTSpace} (hrel : v ∈ relativeWeight n)
    (hblk : v ∈ blkSup n (· = i)) : v ∈ blkW hA n hp i :=
  ⟨⟨v, hrel⟩, hblk, rfl⟩

theorem hN_mem_blkW {n : ℤ} (hp : IsPosOn ((endpointKahler hA).geometry n).P ⊤)
    {a b : ℤ × ℤ} (hb : b + shQm = a) {q q1 : ℤ} (hq : q + 1 = q1) {v : BRSTSpace}
    (hv : v ∈ blkW hA n hp (a, q)) : hN (sN n.toNat) v ∈ blkW hA n hp (b, q1) := by
  obtain ⟨u, hu, rfl⟩ := hv
  subst hq
  exact mem_blkW_of hA hp (hN_mem_relativeWeight hA hb u hu _)
    (hN_goodSup hb (blk_mem_goodSup hA u hu) _)

theorem dN_mem_blkW {n : ℤ} (hp : IsPosOn ((endpointKahler hA).geometry n).P ⊤)
    {a c : ℤ × ℤ} (hc : a + shQm = c) {q q' : ℤ} (hq : q' + 1 = q) {v : BRSTSpace}
    (hv : v ∈ blkW hA n hp (a, q)) : dN hA (sN n.toNat) v ∈ blkW hA n hp (c, q') := by
  obtain ⟨u, hu, rfl⟩ := hv
  rw [show ((relativeWeight n).subtype u) = (((⟨u, hu⟩ : (endpointBlocks hA n hp).blk (a, q)) :
    relativeWeight n) : BRSTSpace) from rfl, ← comp_coe_eq_dN' hA hp hc hq]
  exact ⟨_, ((endpointBlocks hA n hp).comp a c q q' ⟨u, hu⟩).2, rfl⟩

/-- `ΔN` preserves the ambient image of a block. -/
theorem ΔN_mem_blkW {n : ℤ} (hp : IsPosOn ((endpointKahler hA).geometry n).P ⊤)
    (a : ℤ × ℤ) (q : ℤ) {v : BRSTSpace} (hv : v ∈ blkW hA n hp (a, q)) :
    ΔN hA (sN n.toNat) v ∈ blkW hA n hp (a, q) := by
  rw [← dN_hN_add]
  refine Submodule.add_mem _ ?_ ?_
  · exact dN_mem_blkW hA hp (a := a - shQm) (c := a) (by abel) (q := q + 1) (q' := q) rfl
      (hN_mem_blkW hA hp (a := a) (b := a - shQm) (by abel) (q := q) (q1 := q + 1) rfl hv)
  · exact hN_mem_blkW hA hp (a := a + shQm) (b := a) rfl (q := q - 1) (q1 := q) (by ring)
      (dN_mem_blkW hA hp (a := a) (c := a + shQm) rfl (q := q) (q' := q - 1) (by ring) hv)

theorem blkW_le_rel {n : ℤ} (hp : IsPosOn ((endpointKahler hA).geometry n).P ⊤)
    (i : (ℤ × ℤ) × ℤ) : blkW hA n hp i ≤ relativeWeight n := by
  rintro _ ⟨v, -, rfl⟩
  exact v.2

instance blkW_finite {n : ℤ} (hp : IsPosOn ((endpointKahler hA).geometry n).P ⊤)
    (i : (ℤ × ℤ) × ℤ) : FiniteDimensional ℂ (blkW hA n hp i) :=
  Submodule.finiteDimensional_of_le (blkW_le_rel hA hp i)

theorem exists_blk_of_mem_blkW {n : ℤ} (hp : IsPosOn ((endpointKahler hA).geometry n).P ⊤)
    {i : (ℤ × ℤ) × ℤ} {v : BRSTSpace} (hv : v ∈ blkW hA n hp i) :
    ∃ y : (endpointBlocks hA n hp).blk i, ((y : relativeWeight n) : BRSTSpace) = v := by
  obtain ⟨y, hy, rfl⟩ := hv
  exact ⟨⟨y, hy⟩, rfl⟩

theorem comp_eq_of {n : ℤ} (hp : IsPosOn ((endpointKahler hA).geometry n).P ⊤)
    {a b : ℤ × ℤ} (hb : b + shQm = a) {q q' : ℤ} (hq : q' + 1 = q)
    (y : (endpointBlocks hA n hp).blk (b, q)) (x : (endpointBlocks hA n hp).blk (a, q'))
    (h : dN hA (sN n.toNat) ((y : relativeWeight n) : BRSTSpace) =
      ((x : relativeWeight n) : BRSTSpace)) :
    (endpointBlocks hA n hp).comp b a q q' y = x := by
  apply Subtype.ext
  apply Subtype.ext
  rw [comp_coe_eq_dN' hA hp hb hq y]
  exact h

/-- Generic: an endomorphism preserving a finite-dimensional subspace and injective on it is
surjective onto it. -/
theorem exists_preimage_of_injOn {V : Type*} [AddCommGroup V] [Module ℂ V] (W : Submodule ℂ V)
    [FiniteDimensional ℂ W] (f : V →ₗ[ℂ] V) (hW : ∀ v ∈ W, f v ∈ W)
    (hinj : ∀ v ∈ W, f v = 0 → v = 0) : ∀ x ∈ W, ∃ z ∈ W, f z = x := by
  intro x hx
  have hi : Function.Injective (f.restrict hW) := by
    refine (injective_iff_map_eq_zero _).mpr fun v hv => ?_
    exact Subtype.ext (hinj v v.2 (congrArg Subtype.val hv))
  obtain ⟨z, hz⟩ := (LinearMap.injective_iff_surjective.mp hi) ⟨x, hx⟩
  exact ⟨z, z.2, congrArg Subtype.val hz⟩

/-- **Generic Koszul exactness from a native homotopy.** Let `B` be antighost-count blocks of
a finite-dimensional Kähler complex on `K`, embedded in an ambient space `E` by `ι`. Suppose the
block components `K_a,q → K_{a+shQm},q-1` of `Q⁻` are the restrictions of an ambient operator
`d`, an ambient `h` maps the images of blocks to the images of the blocks below, and
`Δ = d h + h d` commutes with `d`, is injective on the images of blocks of positive antighost
number, and every `w` in the image of a block with `Δ w = 0` has `h w = 0`. Then `d_K` is exact in
positive antighost number. -/
theorem kExactAt_of_native {E K : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup K]
    [Module ℂ K] [FiniteDimensional ℂ K] {C : KahlerComplex K} (B : KoszulBlocks C)
    (ι : K →ₗ[ℂ] E) (hι : Function.Injective ι) (d h Δ : E →ₗ[ℂ] E)
    (H1 : ∀ (a c : ℤ × ℤ), a + shQm = c → ∀ (q q' : ℤ), q' + 1 = q → ∀ x : B.blk (a, q),
      ι (B.comp a c q q' x : K) = d (ι (x : K)))
    (H2 : ∀ (a b : ℤ × ℤ), b + shQm = a → ∀ (q q1 : ℤ), q + 1 = q1 →
      ∀ v ∈ (B.blk (a, q)).map ι, h v ∈ (B.blk (b, q1)).map ι)
    (H3 : ∀ v, d (h v) + h (d v) = Δ v) (H3' : ∀ v, Δ (d v) = d (Δ v))
    (H4 : ∀ (a : ℤ × ℤ) (q : ℕ), ∀ v ∈ (B.blk (a, ((q + 1 : ℕ) : ℤ))).map ι, Δ v = 0 → v = 0)
    (H5 : ∀ (a : ℤ × ℤ) (q : ℕ), ∀ w ∈ (B.blk (a, (q : ℤ))).map ι, Δ w = 0 → h w = 0)
    {b a : ℤ × ℤ} (hb : b + shQm = a) (p : ℕ) : B.KExactAt b a p := by
  intro x hx
  -- `d x = 0`
  have hdx : d (ι (x : K)) = 0 := by
    rw [← H1 a (a + shQm) rfl _ _ (by push_cast; ring) x, hx]
    simp
  have hxW : ι (x : K) ∈ (B.blk (a, ((p + 1 : ℕ) : ℤ))).map ι := ⟨x, x.2, rfl⟩
  -- `Δ` preserves the image of the block
  have hΔW : ∀ v ∈ (B.blk (a, ((p + 1 : ℕ) : ℤ))).map ι,
      Δ v ∈ (B.blk (a, ((p + 1 : ℕ) : ℤ))).map ι := by
    intro v hv
    rw [← H3]
    refine Submodule.add_mem _ ?_ ?_
    · obtain ⟨u, hu, hu'⟩ := H2 a b hb _ (((p + 1 : ℕ) : ℤ) + 1) rfl v hv
      rw [← hu', ← H1 b a hb _ ((p + 1 : ℕ) : ℤ) rfl ⟨u, hu⟩]
      exact ⟨_, (B.comp b a _ _ ⟨u, hu⟩).2, rfl⟩
    · obtain ⟨u, hu, rfl⟩ := hv
      rw [← H1 a (a + shQm) rfl _ (p : ℤ) (by push_cast; ring) ⟨u, hu⟩]
      exact H2 (a + shQm) a rfl (p : ℤ) _ (by push_cast; ring) _
        ⟨_, (B.comp a (a + shQm) _ _ ⟨u, hu⟩).2, rfl⟩
  haveI : FiniteDimensional ℂ ((B.blk (a, ((p + 1 : ℕ) : ℤ))).map ι) :=
    Module.Finite.map _ _
  obtain ⟨z, hzW, hz⟩ := exists_preimage_of_injOn _ Δ hΔW
    (fun v hv hv0 => H4 a p v hv hv0) _ hxW
  -- the boundary part vanishes
  have hdzW : d z ∈ (B.blk (a + shQm, (p : ℤ))).map ι := by
    obtain ⟨u, hu, rfl⟩ := hzW
    rw [← H1 a (a + shQm) rfl _ (p : ℤ) (by push_cast; ring) ⟨u, hu⟩]
    exact ⟨_, (B.comp a (a + shQm) _ _ ⟨u, hu⟩).2, rfl⟩
  have hΔdz : Δ (d z) = 0 := by rw [H3', hz, hdx]
  have hhdz : h (d z) = 0 := H5 (a + shQm) p _ hdzW hΔdz
  -- the preimage
  obtain ⟨u, hu, hyc⟩ := H2 a b hb _ ((((p + 1 : ℕ) : ℤ)) + 1) rfl z hzW
  have hq : (((p + 1 : ℕ) : ℤ)) + 1 = ((p + 1 + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [hq] at hu
  refine ⟨⟨u, hu⟩, ?_⟩
  apply Subtype.ext
  apply hι
  rw [H1 b a hb _ _ (by push_cast; ring) ⟨u, hu⟩]
  change d (ι u) = ι (x : K)
  rw [hyc, ← hz, ← H3, hhdz, add_zero]

/-- **Koszul exactness of the actual `d_K` on the endpoint blocks.** -/
theorem kExactAt_endpoint {n : ℤ} (hp : IsPosOn ((endpointKahler hA).geometry n).P ⊤)
    {b a : ℤ × ℤ} (hb : b + shQm = a) (p : ℕ) :
    (endpointBlocks hA n hp).KExactAt b a p := by
  refine kExactAt_of_native (endpointBlocks hA n hp) (relativeWeight n).subtype
    Subtype.val_injective (dN hA (sN n.toNat)) (hN (sN n.toNat)) (ΔN hA (sN n.toNat))
    ?_ ?_ (dN_hN_add hA _) (ΔN_dN hA _) ?_ ?_ hb p
  · intro a c hc q q' hq x
    exact comp_coe_eq_dN' hA hp hc hq x
  · intro a b hb q q1 hq v hv
    exact hN_mem_blkW hA hp hb hq hv
  · intro a q v hv hv0
    refine ΔN_add_injective hA n.toNat (q0 := ((q + 1 : ℕ) : ℤ)) (c := 0) (by push_cast; omega)
      (goodSup_le_lapSup (blkW_le_goodSup hA hp _ hv)) ?_
    rw [hv0, Nat.cast_zero, zero_smul, add_zero]
  · intro a q w hw hw0
    refine hN_eq_zero_of _ fun qq hqq => ?_
    have h := mDerB_ΔN hA (sN n.toNat) hqq w
    rw [hw0, map_zero] at h
    refine ΔN_add_injective hA n.toNat (q0 := (q : ℤ)) (c := 1) (by omega)
      (mDerB_lapSup n.toNat _ qq (goodSup_le_lapSup (blkW_le_goodSup hA hp _ hw))) ?_
    rw [Nat.cast_one, one_smul]
    exact h.symm

/-- **`KExact` for the actual endpoint blocks, at every bidegree.** -/
theorem kExact_endpoint {n : ℤ} (hp : IsPosOn ((endpointKahler hA).geometry n).P ⊤)
    (a : ℤ × ℤ) : (endpointBlocks hA n hp).KExact a :=
  fun p => ⟨kExactAt_endpoint hA hp (by abel) p, kExactAt_endpoint hA hp rfl p⟩

end

end VOA.KoszulResidual
