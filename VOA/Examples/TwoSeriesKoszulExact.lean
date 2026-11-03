/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.KoszulResidualEndpoint
import VOA.Examples.TwoSeriesKoszulHomotopy

/-!
# Level-generic port of `KoszulResidualExact`, `KoszulResidualEndpoint`
-/

namespace VOA.TwoSeries

open VOA.ConcreteHodge VOA.KoszulResidual VOA.KoszulConcrete VOA.SymbolModel VOA.CyclicEval
open VOA.GradedUnitaryCohomology VOA.VertexOperatorAlgebra Sl2CosetConcrete Sl2SemiInfinite
open AffineSl2GeneralRigidity AffineSl2BelowCritical VOA.LeeYangTransferAssembly VOA.SympFerm
open VOA.Ghost
open scoped TensorProduct

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

universe u v w

variable (L : CosetLevels)

/-! ## Port of `KoszulResidualExact` -/


variable (hA : GradedUnitary (affineForm L) (affineRealStructure L) (affineFlag L))

/-- The internal joint grading used by the endpoint blocks. -/
abbrev hIB : DirectSum.IsInternal (blockB L) :=
  (blockB_isInternal L) hA LevelOneUnitary.bUnitary unitWeight unitWeight_pos

/-! ### Antighost anticommutation and relative states -/

theorem antighostZero_hN (N : ℕ) (a : Fin 3) (v : (BRSTSpace L)) :
    antighostZero (matterSVA L) a ((hN L) (sN N) v) = -(hN L) (sN N) (antighostZero (matterSVA L) a v) := by
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

theorem hN_mem_relativeCarrier (N : ℕ) {v : (BRSTSpace L)}
    (hv : v ∈ relativeCarrier (matterAction L).toAffineSl2Action) :
    (hN L) (sN N) v ∈ relativeCarrier (matterAction L).toAffineSl2Action := by
  rw [mem_relativeCarrier] at hv ⊢
  refine ⟨fun a => ?_, fun a => ?_⟩
  · rw [totalZero_hN, hv.1 a, map_zero]
  · rw [antighostZero_hN, hv.2 a, map_zero, neg_zero]

/-! ### Block vectors in joint pieces -/

/-- The `c₀`-free joint pieces of a block. -/
def goodSup (n : ℤ) (b : (ℤ × ℤ) × ℤ) : Submodule ℂ (BRSTSpace L) :=
  ⨆ (j : KF × ℤ) (_ : bIdx j = b ∧ wIdx j = (n : ℂ) ∧ j.1.2 = 0), (blockB L) j

theorem iproj_eq_zero_of_c0 {x : (BRSTSpace L)} (hx : x ∈ ⨆ (k : KF) (_ : k.2 = 0), (brstDegF L) k)
    {j : KF × ℤ} (hj : j.1.2 ≠ 0) : iproj ((hIB L) hA) j x = 0 := by
  refine Submodule.iSup_induction _ (motive := fun x => iproj ((hIB L) hA) j x = 0) hx ?_
    (map_zero _) (fun x y hx hy => by beta_reduce at hx hy ⊢; rw [map_add, hx, hy, add_zero])
  intro k y hy
  refine Submodule.iSup_induction _ (motive := fun x => iproj ((hIB L) hA) j x = 0) hy ?_
    (map_zero _) (fun x y hx hy => by beta_reduce at hx hy ⊢; rw [map_add, hx, hy, add_zero])
  intro hk z hz
  exact iproj_eq_zero_of_weight ((hIB L) hA)
    ((brstDegF_isInternal L) hA LevelOneUnitary.bUnitary unitWeight unitWeight_pos)
    (fun j : KF × ℤ => j.1) (blockB_le_brstDegF L) hz (fun e => hj (by simp only at e; rw [e]; exact hk))

include hA in
/-- **A block vector lies in the `c₀`-free joint pieces of its block.** -/
theorem blk_mem_goodSup {n : ℤ} {b : (ℤ × ℤ) × ℤ} (x : (relativeWeight L) n) (hx : x ∈ (blkE L) n b) :
    (x : (BRSTSpace L)) ∈ (goodSup L) n b := by
  refine mem_iSup_of_iproj ((hIB L) hA) _ fun j hj => ?_
  by_cases h1 : bIdx j = b ∧ wIdx j = (n : ℂ)
  · have hc := (relative_c0free L) hA LevelOneUnitary.bUnitary unitWeight unitWeight_pos
      (z := (x : (BRSTSpace L))) (fun a => ((mem_relativeCarrier _ _).mp x.2.1).2 a)
    exact (iproj_eq_zero_of_c0 L) hA hc (fun h => hj ⟨h1.1, h1.2, h⟩)
  · have hx' : (x : (BRSTSpace L)) ∈ (blkSup L) n (· = b) := hx
    refine (iproj_blkSup_eq_zero L) n hA LevelOneUnitary.bUnitary unitWeight unitWeight_pos hx' ?_
    by_cases h2 : bIdx j = b
    · exact Or.inr fun h => h1 ⟨h2, h⟩
    · exact Or.inl h2

/-! ### The block projection through an ambient decomposition -/

/-- The joint pieces outside a block index (or with negative `c₀`). -/
def NTp (T : (ℤ × ℤ) × ℤ) : Submodule ℂ (BRSTSpace L) :=
  ⨆ (j' : KF × ℤ) (_ : bIdx j' ≠ T ∨ j'.1.2 < 0), (blockB L) j'

theorem NTsup_eq (j : KF × ℤ) : (NTsup L) j = (NTp L) (bIdx (j + δT)) := rfl

/-- **The block projection through an ambient decomposition.** -/
theorem pr_coe_eq {n : ℤ} (hp : IsPosOn (((endpointKahler L) hA).geometry n).P ⊤)
    (T : (ℤ × ℤ) × ℤ) (y : (relativeWeight L) n) {z' : (BRSTSpace L)} (hz' : z' ∈ (blkSup L) n (· = T))
    (hyz : (y : (BRSTSpace L)) - z' ∈ (NTp L) T) :
    ((((endpointBlocks L) hA n hp).pr T y : (relativeWeight L) n) : (BRSTSpace L)) = z' := by
  obtain ⟨p, hpdef⟩ : ∃ p, p = ((endpointBlocks L) hA n hp).pr T y := ⟨_, rfl⟩
  rw [← hpdef]
  have hp1 : (p : (BRSTSpace L)) ∈ (blkSup L) n (· = T) := by
    rw [hpdef]; exact ((endpointBlocks L) hA n hp).pr_mem T y
  -- `y - p` lies in the other blocks
  have hyp : y - p ∈ ⨆ (b : (ℤ × ℤ) × ℤ) (_ : b ≠ T), (blkE L) n b := by
    rw [hpdef]; exact KoszulBlocks.sub_pr_mem ((endpointBlocks L) hA n hp) T y
  have hyp' : ((y - p : (relativeWeight L) n) : (BRSTSpace L)) ∈
      ⨆ (j : KF × ℤ) (_ : bIdx j ≠ T), (blockB L) j := by
    refine Submodule.iSup_induction _ (motive := fun v : (relativeWeight L) n => (v : (BRSTSpace L)) ∈
      ⨆ (j : KF × ℤ) (_ : bIdx j ≠ T), (blockB L) j) hyp ?_
      (by simp) (fun v w hv hw => by
        beta_reduce at hv hw ⊢; rw [Submodule.coe_add]; exact Submodule.add_mem _ hv hw)
    intro b v hv
    refine Submodule.iSup_induction _ (motive := fun v : (relativeWeight L) n => (v : (BRSTSpace L)) ∈
      ⨆ (j : KF × ℤ) (_ : bIdx j ≠ T), (blockB L) j) hv ?_
      (by simp) (fun v w hv hw => by
        beta_reduce at hv hw ⊢; rw [Submodule.coe_add]; exact Submodule.add_mem _ hv hw)
    intro hb u hu
    have hu' : (u : (BRSTSpace L)) ∈ (blkSup L) n (· = b) := hu
    have hle : (blkSup L) n (· = b) ≤ ⨆ (j : KF × ℤ) (_ : bIdx j ≠ T), (blockB L) j :=
      iSup_le fun j => iSup_le fun hj => le_iSup_of_le j (le_iSup_of_le (by rw [hj.1]; exact hb)
        le_rfl)
    exact hle hu'
  refine eq_of_iproj_eq ((hIB L) hA) fun j' => ?_
  by_cases hj' : bIdx j' = T
  · by_cases hc : j'.1.2 < 0
    · have h1 := iproj_mem ((hIB L) hA) j' (p : (BRSTSpace L))
      have h2 := iproj_mem ((hIB L) hA) j' z'
      rw [(blockB_eq_bot_of_c0 L) (by omega), Submodule.mem_bot] at h1 h2
      rw [h1, h2]
    · have e1 : iproj ((hIB L) hA) j' ((y : (BRSTSpace L)) - z') = 0 :=
        iproj_eq_zero_of_mem_iSup ((hIB L) hA) _ hyz (by
          rintro (h | h)
          · exact h hj'
          · exact hc h)
      have e2 : iproj ((hIB L) hA) j' (((y - p : (relativeWeight L) n) : (BRSTSpace L))) = 0 :=
        iproj_eq_zero_of_mem_iSup ((hIB L) hA) _ hyp' (fun h => h hj')
      rw [map_sub, sub_eq_zero] at e1
      rw [Submodule.coe_sub, map_sub, sub_eq_zero] at e2
      rw [← e2, e1]
  · rw [(iproj_blkSup_eq_zero L) n hA LevelOneUnitary.bUnitary unitWeight unitWeight_pos hp1
      (Or.inl hj'), (iproj_blkSup_eq_zero L) n hA LevelOneUnitary.bUnitary unitWeight unitWeight_pos
      hz' (Or.inl hj')]

/-! ### The actual `d_K` is the native Koszul differential -/

theorem goodSup_induction {n : ℤ} {b : (ℤ × ℤ) × ℤ} (Φ : (BRSTSpace L) → Prop) (h0 : Φ 0)
    (hadd : ∀ x y, Φ x → Φ y → Φ (x + y))
    (hj : ∀ j : KF × ℤ, bIdx j = b → wIdx j = (n : ℂ) → j.1.2 = 0 →
      ∀ z ∈ (blockB L) j, Φ z) :
    ∀ x ∈ (goodSup L) n b, Φ x := by
  intro x hx
  refine Submodule.iSup_induction _ (motive := Φ) hx ?_ h0 hadd
  intro j y hy
  refine Submodule.iSup_induction _ (motive := Φ) hy ?_ h0 hadd
  intro hj' z hz
  exact hj j hj'.1 hj'.2.1 hj'.2.2 z hz

/-- `Q - (dN L)` and `(dN L)` on a good block vector. -/
theorem Q_dN_goodSup {n : ℤ} {a : ℤ × ℤ} {q : ℤ} {x : (BRSTSpace L)} (hx : x ∈ (goodSup L) n (a, q)) :
    semiInfiniteQ (matterAction L).toAffineSl2Action x - (dN L) hA (sN n.toNat) x ∈
        (NTp L) (a + shQm, q - 1) ∧
      (dN L) hA (sN n.toNat) x ∈ (blkSup L) n (· = (a + shQm, q - 1)) := by
  refine (goodSup_induction L) (fun x => semiInfiniteQ (matterAction L).toAffineSl2Action x -
      (dN L) hA (sN n.toNat) x ∈ (NTp L) (a + shQm, q - 1) ∧
      (dN L) hA (sN n.toNat) x ∈ (blkSup L) n (· = (a + shQm, q - 1))) (by simp)
    (fun x y hx hy => ⟨by rw [map_add, map_add, add_sub_add_comm]; exact Submodule.add_mem _ hx.1 hy.1,
      by rw [map_add]; exact Submodule.add_mem _ hx.2 hy.2⟩) ?_ x hx
  intro j hb hw hc z hz
  have hT : bIdx (j + δT) = (a + shQm, q - 1) := by
    rw [bIdx_add_δT]
    have h1 : j.1.1.1 = a := congrArg Prod.fst hb
    have h2 : j.2 = q := congrArg Prod.snd hb
    rw [h1, h2]
  refine ⟨?_, ?_⟩
  · have h := (Q_sub_dN_mem L) hA n.toNat hc (n0 := n) hw (le_toNat n) z hz
    rwa [NTsup_eq, hT] at h
  · exact Submodule.mem_iSup_of_mem (j + δT) (Submodule.mem_iSup_of_mem
      ⟨hT, by rw [wIdx_add_δT]; exact hw⟩ ((dN_mem_blockB L) hA _ j z hz))

/-- **The actual block component `d_K` of `Q⁻` is the native Koszul differential.** -/
theorem comp_coe_eq_dN {n : ℤ} (hp : IsPosOn (((endpointKahler L) hA).geometry n).P ⊤)
    (a : ℤ × ℤ) {q q' : ℤ} (hq : q' + 1 = q)
    (x : ((endpointBlocks L) hA n hp).blk (a, q)) :
    (((((endpointBlocks L) hA n hp).comp a (a + shQm) q q' x : (relativeWeight L) n)) : (BRSTSpace L)) =
      (dN L) hA (sN n.toNat) ((x : (relativeWeight L) n) : (BRSTSpace L)) := by
  have hq' : q' = q - 1 := by omega
  subst hq'
  rw [KoszulBlocks.comp_coe, KoszulBlocks.pr_Qm_eq_pr_D _ (((endpointBlocks L) hA n hp).le_deg a q x.2),
    ((endpointKahler L) hA).model_D n hp]
  have hgood := (blk_mem_goodSup L) hA (x : (relativeWeight L) n) x.2
  obtain ⟨h1, h2⟩ := (Q_dN_goodSup L) hA hgood
  refine (pr_coe_eq L) hA hp _ _ h2 ?_
  rw [relativeDifferential_coe, brstComplex_Q]
  exact h1

/-! ### The homotopy preserves blocks -/

theorem blkSup_le_grading (n : ℤ) (S : (ℤ × ℤ) × ℤ → Prop) :
    (blkSup L) n S ≤ (brstSVA L).grading (n : ℂ) :=
  iSup_le fun j => iSup_le fun hj => by
    have h := (blockB_le_weight L) unitWeight j
    rw [show j.1.1.2 = (n : ℂ) from hj.2] at h
    exact h

/-- **`(hN L)` maps a block vector to the block below.** -/
theorem hN_goodSup {n : ℤ} {a b : ℤ × ℤ} (hb : b + shQm = a) {q : ℤ} {x : (BRSTSpace L)}
    (hx : x ∈ (goodSup L) n (a, q)) (N : ℕ) : (hN L) (sN N) x ∈ (blkSup L) n (· = (b, q + 1)) := by
  refine (goodSup_induction L) (fun x => (hN L) (sN N) x ∈ (blkSup L) n (· = (b, q + 1))) (by simp)
    (fun x y hx hy => by beta_reduce at hx hy ⊢; rw [map_add]; exact Submodule.add_mem _ hx hy)
    ?_ x hx
  intro j hbj hw hc z hz
  have hT : bIdx (j + δH) = (b, q + 1) := by
    rw [bIdx_add_δH]
    have h1 : j.1.1.1 = a := congrArg Prod.fst hbj
    have h2 : j.2 = q := congrArg Prod.snd hbj
    rw [h1, h2, ← hb, add_sub_cancel_right]
  exact Submodule.mem_iSup_of_mem (j + δH) (Submodule.mem_iSup_of_mem
    ⟨hT, by rw [wIdx_add_δH]; exact hw⟩ ((hN_mem_blockB L) _ j z hz))

include hA in
theorem hN_mem_relativeWeight {n : ℤ} {a b : ℤ × ℤ} (hb : b + shQm = a) {q : ℤ}
    (x : (relativeWeight L) n) (hx : x ∈ (blkE L) n (a, q)) (N : ℕ) :
    (hN L) (sN N) (x : (BRSTSpace L)) ∈ (relativeWeight L) n := by
  have hs := (hN_goodSup L) hb ((blk_mem_goodSup L) hA x hx) N
  exact ⟨(hN_mem_relativeCarrier L) N x.2.1, (blkSup_le_grading L) n _ hs⟩

/-! ### Injectivity of the Koszul Laplacian -/

/-- The joint pieces of antighost number `q₀` and integral weight `≤ N`. -/
def lapSup (N : ℕ) (q0 : ℤ) : Submodule ℂ (BRSTSpace L) :=
  ⨆ (j : KF × ℤ) (_ : j.2 = q0 ∧ ∃ n0 : ℤ, n0 ≤ N ∧ j.1.1.2 = (n0 : ℂ)), (blockB L) j

theorem NbB_lapSup (N : ℕ) (q0 : ℤ) {v : (BRSTSpace L)} (hv : v ∈ (lapSup L) N q0) :
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
  rw [(NbB_blockB L) N hw hn0 z hz, hq]

theorem rTensor_injective_ghost {f : Module.End ℂ (MatterSpace L)} (hf : Function.Injective f) :
    Function.Injective (TensorProduct.map f (LinearMap.id : Module.End ℂ Sl2GhostSpace)) := by
  have h := Module.Flat.rTensor_preserves_injective_linearMap (R := ℂ) (M := Sl2GhostSpace) f hf
  exact h

/-- **`(ΔN L) + c` is injective on joint pieces of antighost number `q₀` with `q₀ + c ≥ 1`.** -/
theorem ΔN_add_injective (N : ℕ) {q0 : ℤ} {c : ℕ} (hc : 1 ≤ q0 + c) {v : (BRSTSpace L)}
    (hv : v ∈ (lapSup L) N q0) (h : (ΔN L) hA (sN N) v + (c : ℂ) • v = 0) : v = 0 := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (k : ℤ) = q0 + c := ⟨(q0 + c).toNat, by omega⟩
  have hk1 : 1 ≤ k := by omega
  have hf : Function.Injective ((mL L) hA (sN N) + (k : ℂ) •
      (LinearMap.id : Module.End ℂ (MatterSpace L))) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    exact (mL_add_injective L) hA (sN N) hk1 (by simpa using hw)
  apply (rTensor_injective_ghost L) hf
  rw [map_zero, ← h, ΔN, LinearMap.add_apply, (NbB_lapSup L) N q0 hv]
  rw [show TensorProduct.map ((mL L) hA (sN N) + (k : ℂ) • (LinearMap.id : Module.End ℂ (MatterSpace L)))
      (LinearMap.id : Module.End ℂ Sl2GhostSpace) = TensorProduct.map ((mL L) hA (sN N))
      (LinearMap.id : Module.End ℂ Sl2GhostSpace) + (k : ℂ) •
        (LinearMap.id : Module.End ℂ (BRSTSpace L)) by
    rw [TensorProduct.map_add_left, TensorProduct.map_smul_left, TensorProduct.map_id]]
  rw [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply, add_assoc, ← add_smul]
  have hkc : (k : ℂ) = (q0 : ℂ) + (c : ℂ) := by exact_mod_cast hk
  rw [hkc]

theorem goodSup_le_lapSup {n : ℤ} {a : ℤ × ℤ} {q : ℤ} :
    (goodSup L) n (a, q) ≤ (lapSup L) n.toNat q :=
  iSup_le fun j => iSup_le fun hj => le_iSup_of_le j (le_iSup_of_le
    ⟨congrArg Prod.snd hj.1, n, le_toNat n, hj.2.1⟩ le_rfl)

theorem mDerB_lapSup (N : ℕ) (q0 : ℤ) (qq : LexLetter) {v : (BRSTSpace L)} (hv : v ∈ (lapSup L) N q0) :
    (mDerB L) qq v ∈ (lapSup L) N q0 := by
  refine Submodule.iSup_induction _ (motive := fun v => (mDerB L) qq v ∈ (lapSup L) N q0) hv ?_
    (by simp) (fun x y hx hy => by beta_reduce at hx hy ⊢; rw [map_add]; exact Submodule.add_mem _ hx hy)
  intro j y hy
  refine Submodule.iSup_induction _ (motive := fun v => (mDerB L) qq v ∈ (lapSup L) N q0) hy ?_
    (by simp) (fun x y hx hy => by beta_reduce at hx hy ⊢; rw [map_add]; exact Submodule.add_mem _ hx hy)
  intro hj z hz
  obtain ⟨hq, n0, hn0, hw⟩ := hj
  refine Submodule.mem_iSup_of_mem (j + ((-(eq qq), 0), 0)) (Submodule.mem_iSup_of_mem
    ⟨by simp [hq], n0 - letterWt qq, by omega, ?_⟩ ((mDerB_mem_blockB L) qq j z hz))
  simp only [Prod.fst_add, Prod.snd_add, Prod.snd_neg, hw, eq, letterWt]
  push_cast; ring

/-! ### Koszul exactness -/

theorem comp_coe_eq_dN' {n : ℤ} (hp : IsPosOn (((endpointKahler L) hA).geometry n).P ⊤)
    {a c : ℤ × ℤ} (hc : a + shQm = c) {q q' : ℤ} (hq : q' + 1 = q)
    (x : ((endpointBlocks L) hA n hp).blk (a, q)) :
    (((((endpointBlocks L) hA n hp).comp a c q q' x : (relativeWeight L) n)) : (BRSTSpace L)) =
      (dN L) hA (sN n.toNat) ((x : (relativeWeight L) n) : (BRSTSpace L)) := by
  subst hc
  exact (comp_coe_eq_dN L) hA hp a hq x

/-- The ambient image of a block. -/
abbrev blkW (n : ℤ) (hp : IsPosOn (((endpointKahler L) hA).geometry n).P ⊤) (i : (ℤ × ℤ) × ℤ) :
    Submodule ℂ (BRSTSpace L) :=
  (((endpointBlocks L) hA n hp).blk i).map ((relativeWeight L) n).subtype

theorem blkW_le_goodSup {n : ℤ} (hp : IsPosOn (((endpointKahler L) hA).geometry n).P ⊤)
    (i : (ℤ × ℤ) × ℤ) : (blkW L) hA n hp i ≤ (goodSup L) n i := by
  rintro _ ⟨v, hv, rfl⟩
  exact (blk_mem_goodSup L) hA v hv

theorem mem_blkW_of {n : ℤ} (hp : IsPosOn (((endpointKahler L) hA).geometry n).P ⊤)
    {i : (ℤ × ℤ) × ℤ} {v : (BRSTSpace L)} (hrel : v ∈ (relativeWeight L) n)
    (hblk : v ∈ (blkSup L) n (· = i)) : v ∈ (blkW L) hA n hp i :=
  ⟨⟨v, hrel⟩, hblk, rfl⟩

theorem hN_mem_blkW {n : ℤ} (hp : IsPosOn (((endpointKahler L) hA).geometry n).P ⊤)
    {a b : ℤ × ℤ} (hb : b + shQm = a) {q q1 : ℤ} (hq : q + 1 = q1) {v : (BRSTSpace L)}
    (hv : v ∈ (blkW L) hA n hp (a, q)) : (hN L) (sN n.toNat) v ∈ (blkW L) hA n hp (b, q1) := by
  obtain ⟨u, hu, rfl⟩ := hv
  subst hq
  exact (mem_blkW_of L) hA hp ((hN_mem_relativeWeight L) hA hb u hu _)
    ((hN_goodSup L) hb ((blk_mem_goodSup L) hA u hu) _)

/-- **Koszul exactness of the actual `d_K` on the endpoint blocks.** -/
theorem kExactAt_endpoint {n : ℤ} (hp : IsPosOn (((endpointKahler L) hA).geometry n).P ⊤)
    {b a : ℤ × ℤ} (hb : b + shQm = a) (p : ℕ) :
    ((endpointBlocks L) hA n hp).KExactAt b a p := by
  refine kExactAt_of_native ((endpointBlocks L) hA n hp) ((relativeWeight L) n).subtype
    Subtype.val_injective ((dN L) hA (sN n.toNat)) ((hN L) (sN n.toNat)) ((ΔN L) hA (sN n.toNat))
    ?_ ?_ ((dN_hN_add L) hA _) ((ΔN_dN L) hA _) ?_ ?_ hb p
  · intro a c hc q q' hq x
    exact (comp_coe_eq_dN' L) hA hp hc hq x
  · intro a b hb q q1 hq v hv
    exact (hN_mem_blkW L) hA hp hb hq hv
  · intro a q v hv hv0
    refine (ΔN_add_injective L) hA n.toNat (q0 := ((q + 1 : ℕ) : ℤ)) (c := 0) (by push_cast; omega)
      ((goodSup_le_lapSup L) ((blkW_le_goodSup L) hA hp _ hv)) ?_
    rw [hv0, Nat.cast_zero, zero_smul, add_zero]
  · intro a q w hw hw0
    refine (hN_eq_zero_of L) _ fun qq hqq => ?_
    have h := (mDerB_ΔN L) hA (sN n.toNat) hqq w
    rw [hw0, map_zero] at h
    refine (ΔN_add_injective L) hA n.toNat (q0 := (q : ℤ)) (c := 1) (by omega)
      ((mDerB_lapSup L) n.toNat _ qq ((goodSup_le_lapSup L) ((blkW_le_goodSup L) hA hp _ hw))) ?_
    rw [Nat.cast_one, one_smul]
    exact h.symm

/-- **`KExact` for the actual endpoint blocks, at every bidegree.** -/
theorem kExact_endpoint {n : ℤ} (hp : IsPosOn (((endpointKahler L) hA).geometry n).P ⊤)
    (a : ℤ × ℤ) : ((endpointBlocks L) hA n hp).KExact a :=
  fun p => ⟨(kExactAt_endpoint L) hA hp (by abel) p, (kExactAt_endpoint L) hA hp rfl p⟩


/-! ## Port of `KoszulResidualEndpoint` -/


variable (hA : GradedUnitary (affineForm L) (affineRealStructure L) (affineFlag L))

/-- **OPEN (the symbol maps) at weight `n`, degree `r`**: the second component of
`(KoszulResidual L)` — `π₀` on the antighost-free block at `(2r, 0)` into `gr_r A ⊗ L_1` with kernel
exactly the `d_K`-boundaries, `π₁` on the antighost-free block at `(2r + 1, 1)` with kernel
exactly the `d_K`-boundaries, `π₁ ∘ d_CE = (grDiag L) ∘ π₀`, and `π₀` landing in weight `n`. -/
def SymbolResidual (n : ℤ) (hp : IsPosOn (((endpointKahler L) hA).geometry n).P ⊤) (r : ℕ) :
    Type :=
  Σ' S : ((endpointBlocks L) hA n hp).KoszulSymbolMaps (2 * (r : ℤ), 0) ((GrA L) r ⊗[ℂ] BSpace)
    ((grDiag L) r), ∀ x, S.π0 x ∈ tensorWeight ((grDeg L) r) bWeight n

/-- OPEN: the symbol maps at every weight and degree. -/
abbrev EndpointSymbolResidual : Type :=
  ∀ n (hp : IsPosOn (((endpointKahler L) hA).geometry n).P ⊤) (r : ℕ), (SymbolResidual L) hA n hp r

/-- **The Koszul residual from the symbol maps alone**: Koszul exactness is proved. -/
def koszulResidual_of_symbols (S : (EndpointSymbolResidual L) hA) : (EndpointKoszulResidual L) hA :=
  fun n hp r => ⟨(kExact_endpoint L) hA hp (2 * (r : ℤ), 0), S n hp r⟩


end

end VOA.TwoSeries
