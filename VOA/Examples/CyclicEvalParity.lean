/-
Copyright (c) 2026 Fedor Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor Popov
-/
import VOA.Examples.CyclicEvalAssembly
import VOA.Examples.BRSTGoodnessFock

/-!
# No relative states at odd `2R` and ghost number zero

On one `bc` pair, a creation monomial has `2R - gh ≡ #c₀ (mod 2)`: `b`-modes contribute
`1 - (-1) = 2`, nonzero `c`-modes `1 - 1 = 0`, and `c₀` contributes `0 - 1 = -1`. The matter
pieces have even `2R` and ghost number `0`. Relative states are killed by the three antighost
zero modes `b₀^a`, hence fixed by the three `c₀`-parities `1 - 2 c₀^a b₀^a`; but on a piece of
odd `2R - gh` the product of these parities is `-1`. So relative states of odd `2R` at ghost
number zero vanish.

* `parC0_stWordSF` — `(1 - 2 c₀ b₀)(word) = (-1)^{2R - gh} word`, for every word;
* `ghostParity_ghostDeg` — the product of the three `c₀`-parities is `(-1)^{2R - gh}` on
  `ghostDeg`;
* `matterDeg_even` — matter pieces live at even `2R` and ghost number `0`;
* `relDeg_odd_eq_bot` — the interpreted bigraded piece of the relative complex at
  `(2p+1, 0)` is zero, for every standard ghost grading;
* `endpoint_oddZero` — **`EndpointOddVanishing`-type statement for the endpoint geometry**
  (the `odd_zero` field of `LeadingCyclicEvaluation`), proved.

Everything is proved outright.
-/

namespace VOA.ConcreteHodge

open VOA.SympFerm VOA.Ghost Sl2SemiInfinite Sl2CosetConcrete VOA.LeeYangTransferAssembly
open VOA.GradedUnitaryCohomology VOA.VertexOperatorAlgebra
open scoped TensorProduct

noncomputable section
set_option synthInstance.maxHeartbeats 200000

/-! ### One pair -/

/-- `±1` according to the parity of an integer. -/
def psign (n : ℤ) : ℂ := if Even n then 1 else -1

theorem psign_add (a b : ℤ) : psign (a + b) = psign a * psign b := by
  unfold psign
  by_cases ha : Even a <;> by_cases hb : Even b <;> simp [ha, hb, Int.even_add]

/-- The `c₀`-parity `1 - 2 c₀ b₀` of one pair (`c₀ = creBase (0,1)`, `b₀ = annBase (0,1)`). -/
def parC0 : Module.End ℂ FockSF :=
  LinearMap.id - (2 : ℂ) • (creBase (0, 1) ∘ₗ annBase (0, 1))

theorem annBase_creBase (p q : ℕ × Fin 2) (y : FockSF) :
    annBase p (creBase q y) = (if p = q then (1 : ℂ) else 0) • y - creBase q (annBase p y) := by
  rw [annBase, creBase, LinearMap.mulLeft_apply, CliffordAlgebra.contractLeft_ι_mul,
    lapply_single_eq]
  rfl

theorem creBase_creBase_self (p : ℕ × Fin 2) (y : FockSF) : creBase p (creBase p y) = 0 := by
  have h := creBase_anticomm p p y
  have h2 : (2 : ℂ) • creBase p (creBase p y) = 0 := by rw [two_smul]; exact h
  exact (smul_eq_zero.mp h2).resolve_left two_ne_zero

theorem parC0_apply (y : FockSF) :
    parC0 y = y - (2 : ℂ) • creBase (0, 1) (annBase (0, 1) y) := rfl

theorem parC0_creBase (q : ℕ × Fin 2) (y : FockSF) :
    parC0 (creBase q y) = (if q = (0, 1) then (-1 : ℂ) else 1) • creBase q (parC0 y) := by
  rw [parC0_apply, parC0_apply, annBase_creBase, map_sub, map_smul, map_sub, map_smul]
  by_cases hq : q = (0, 1)
  · subst hq
    rw [if_pos rfl, if_pos rfl, one_smul]
    simp only [creBase_creBase_self, smul_zero, sub_zero]
    module
  · rw [if_neg (Ne.symm hq), if_neg hq, zero_smul, zero_sub, one_smul]
    have hc : creBase (0, 1) (creBase q (annBase (0, 1) y)) =
        -creBase q (creBase (0, 1) (annBase (0, 1) y)) :=
      eq_neg_of_add_eq_zero_left (creBase_anticomm _ _ _)
    simp only [hc, neg_neg]

theorem modeParity (q : ℕ × Fin 2) :
    psign (modeR q - ghCharge q.2) = if q = (0, 1) then (-1 : ℂ) else 1 := by
  obtain ⟨k, e⟩ := q
  fin_cases e
  · have : ((k, (0 : Fin 2)) : ℕ × Fin 2) ≠ (0, 1) := by simp
    simp [psign, modeR, ghCharge, this]
  · by_cases hk : k = 0
    · subst hk; simp [psign, modeR, ghCharge]
    · have : ((k, (1 : Fin 2)) : ℕ × Fin 2) ≠ (0, 1) := by simp [hk]
      simp [psign, modeR, ghCharge, this]

/-- **The `c₀`-parity of a word is `(-1)^{2R - gh}`.** -/
theorem parC0_stWordSF (l : SFWord) :
    parC0 (stWordSF l) = psign (wordR l - ghNum l) • stWordSF l := by
  induction l with
  | nil =>
    rw [parC0_apply, stWordSF_nil, ← stWordSF_nil, annBase_stWordSF_nil]
    simp [psign, wordR, ghNum]
  | cons q rest ih =>
    rw [← creBase_stWordSF, parC0_creBase, ih, map_smul, smul_smul, ← modeParity, ← psign_add]
    congr 2
    simp only [wordR, List.map_cons, List.sum_cons, ghNum_cons]
    ring

theorem parC0_fockDeg {j g : ℤ} {w : ℂ} {x : FockSF} (hx : x ∈ fockDeg ((j, g), w)) :
    parC0 x = psign (j - g) • x := by
  rw [fockDeg_eq_wordDeg, wordDeg] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, rfl⟩ := hx
    have hl' : wordIdx l = ((j, g), w) := hl
    have h1 : wordR l = j := congrArg (fun i => i.1.1) hl'
    have h2 : ghNum l = g := congrArg (fun i => i.1.2) hl'
    rw [parC0_stWordSF, h1, h2]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy, smul_add]
  | smul c x _ hx => rw [map_smul, hx, smul_comm]

/-! ### Koszul operators are involutions -/

theorem koszulOp_one_invol {𝒱 : Type*} [AddCommGroup 𝒱] [Module ℂ 𝒱] (P : ParityGrading 𝒱)
    (u : 𝒱) : P.koszulOp 1 (P.koszulOp 1 u) = u := by
  have hu : u ∈ P.parity 0 ⊔ P.parity 1 := by rw [P.isCompl01.sup_eq_top]; exact Submodule.mem_top
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hu
  rw [map_add, P.koszulOp_homog 1 hy, P.koszulOp_homog 1 hz, koszul_zero_right, koszul_one_one,
    one_smul, map_add, map_smul, P.koszulOp_homog 1 hy, P.koszulOp_homog 1 hz,
    koszul_zero_right, koszul_one_one, one_smul, smul_smul]
  norm_num

/-! ### Three pairs -/

/-- Scalar actions on the pieces of two gradings give a scalar action on the tensor grading. -/
theorem tensorDeg_map_scalar {ι : Type*} [AddCommGroup ι] {V W : Type*} [AddCommGroup V]
    [Module ℂ V] [AddCommGroup W] [Module ℂ W] (dV : ι → Submodule ℂ V) (dW : ι → Submodule ℂ W)
    (T : Module.End ℂ V) (S : Module.End ℂ W) (s : ι → ℂ) (hs : ∀ a b, s (a + b) = s a * s b)
    (hT : ∀ i, ∀ x ∈ dV i, T x = s i • x) (hS : ∀ i, ∀ y ∈ dW i, S y = s i • y) (a : ι) :
    ∀ z ∈ tensorDeg dV dW a, TensorProduct.map T S z = s a • z := by
  refine tensorDeg_induction dV dW a (fun z => TensorProduct.map T S z = s a • z) (by simp)
    (fun x y hx hy => by beta_reduce at hx hy ⊢; rw [map_add, hx, hy, smul_add])
    (fun c x hx => by beta_reduce at hx ⊢; rw [map_smul, hx, smul_comm]) ?_
  intro b x hx y hy
  rw [TensorProduct.map_tmul, hT b x hx, hS _ y hy, TensorProduct.smul_tmul_smul]
  congr 1
  rw [← hs, add_sub_cancel]

/-- The sign `(-1)^{2R - gh}` of an index. -/
def idxSign (i : (ℤ × ℤ) × ℂ) : ℂ := psign (i.1.1 - i.1.2)

theorem idxSign_add (a b : (ℤ × ℤ) × ℂ) : idxSign (a + b) = idxSign a * idxSign b := by
  unfold idxSign
  rw [← psign_add]
  congr 1
  simp only [Prod.fst_add, Prod.snd_add]
  ring

theorem parC0_fockDeg' (i : (ℤ × ℤ) × ℂ) (x : FockSF) (hx : x ∈ fockDeg i) :
    parC0 x = idxSign i • x := by
  obtain ⟨⟨j, g⟩, w⟩ := i
  exact parC0_fockDeg hx

/-- The product of the three `c₀`-parities. -/
def ghostParity : Module.End ℂ Sl2GhostSpace :=
  TensorProduct.map (TensorProduct.map parC0 parC0) parC0

/-- The product of the three `c₀`-parities is `(-1)^{2R - gh}` on `ghostDeg`. -/
theorem ghostParity_ghostDeg (i : (ℤ × ℤ) × ℂ) (x : Sl2GhostSpace) (hx : x ∈ ghostDeg i) :
    ghostParity x = idxSign i • x :=
  tensorDeg_map_scalar _ _ _ _ idxSign idxSign_add
    (tensorDeg_map_scalar _ _ _ _ idxSign idxSign_add parC0_fockDeg' parC0_fockDeg')
    parC0_fockDeg' i x hx

theorem ghField_one_zero' : ghField 1 0 = creBase (0, 1) := by
  simp [ghField, creGh]

theorem ghField_zero_negOne' : ghField 0 (-1) = annBase (0, 1) := by
  simp [ghField, annGh]

/-- `1 - 2 c₀^a b₀^a`, as an operator on the three-pair space. -/
theorem parity_zero_eq : TensorProduct.map (TensorProduct.map parC0 LinearMap.id) LinearMap.id =
    LinearMap.id - (2 : ℂ) • (gMode 0 1 (-1) * gMode 0 0 0) := by
  apply TensorProduct.ext'; intro w z
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add w w' hw hw' => rw [TensorProduct.add_tmul, map_add, map_add, hw, hw']
  | tmul x y =>
    rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.mul_apply, gMode_tmul_zero,
      gMode_tmul_zero]
    simp only [TensorProduct.map_tmul, LinearMap.id_apply]
    rw [show (-(-1 : ℤ) - 1) = 0 by norm_num, show (-(0 : ℤ) - 1) = -1 by norm_num,
      ghField_one_zero', ghField_zero_negOne', parC0_apply, TensorProduct.sub_tmul,
      TensorProduct.sub_tmul, TensorProduct.smul_tmul', TensorProduct.smul_tmul']

theorem parity_one_eq : TensorProduct.map (TensorProduct.map LinearMap.id parC0) LinearMap.id =
    LinearMap.id - (2 : ℂ) • (gMode 1 1 (-1) * gMode 1 0 0) := by
  apply TensorProduct.ext'; intro w z
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add w w' hw hw' => rw [TensorProduct.add_tmul, map_add, map_add, hw, hw']
  | tmul x y =>
    rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.mul_apply, gMode_tmul_one,
      gMode_tmul_one, koszulOp_one_invol]
    simp only [TensorProduct.map_tmul, LinearMap.id_apply]
    rw [show (-(-1 : ℤ) - 1) = 0 by norm_num, show (-(0 : ℤ) - 1) = -1 by norm_num,
      ghField_one_zero', ghField_zero_negOne', parC0_apply, TensorProduct.tmul_sub,
      TensorProduct.sub_tmul, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    simp only [TensorProduct.smul_tmul']

theorem parity_two_eq : TensorProduct.map LinearMap.id parC0 =
    LinearMap.id - (2 : ℂ) • (gMode 2 1 (-1) * gMode 2 0 0) := by
  apply TensorProduct.ext'; intro w z
  rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.mul_apply, gMode_tmul_two,
    gMode_tmul_two, koszulOp_one_invol]
  simp only [TensorProduct.map_tmul, LinearMap.id_apply]
  rw [show (-(-1 : ℤ) - 1) = 0 by norm_num, show (-(0 : ℤ) - 1) = -1 by norm_num,
    ghField_one_zero', ghField_zero_negOne', parC0_apply, TensorProduct.tmul_sub,
    TensorProduct.tmul_smul]

theorem ghostParity_eq : ghostParity =
    TensorProduct.map (TensorProduct.map parC0 LinearMap.id) LinearMap.id *
    TensorProduct.map (TensorProduct.map LinearMap.id parC0) LinearMap.id *
    TensorProduct.map LinearMap.id parC0 := by
  apply TensorProduct.ext'; intro w z
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add w w' hw hw' => rw [TensorProduct.add_tmul, map_add, map_add, hw, hw']
  | tmul x y => simp [ghostParity]

/-! ### Matter pieces: even `2R`, ghost number zero -/

/-- A family with pieces only at even `2R` and ghost number `0`. -/
def EvenZero {E : Type*} [AddCommGroup E] [Module ℂ E] (d : (ℤ × ℤ) × ℂ → Submodule ℂ E) :
    Prop :=
  ∀ i, ¬ (Even i.1.1 ∧ i.1.2 = 0) → d i = ⊥

theorem tensorDeg_evenZero {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] {dV : (ℤ × ℤ) × ℂ → Submodule ℂ V} {dW : (ℤ × ℤ) × ℂ → Submodule ℂ W}
    (hV : EvenZero dV) (hW : EvenZero dW) : EvenZero (tensorDeg dV dW) := by
  intro i hi
  rw [eq_bot_iff]
  refine iSup_le fun b => ?_
  by_cases hb : Even b.1.1 ∧ b.1.2 = 0
  · have hib : ¬ (Even (i - b).1.1 ∧ (i - b).1.2 = 0) := by
      rintro ⟨h1, h2⟩
      apply hi
      simp only [Prod.fst_sub, Prod.snd_sub] at h1 h2
      refine ⟨?_, by omega⟩
      have := h1.add hb.1
      simpa using this
    rw [hW _ hib, Submodule.map₂_bot_right]
  · rw [hV b hb, Submodule.map₂_bot_left]

theorem layerDeg_evenZero {𝒱 : Type*} [AddCommGroup 𝒱] [Module ℂ 𝒱]
    {W : VOA.VertexOperatorAlgebra 𝒱} (B : InvariantForm W) (F : GradedFlag W) :
    EvenZero (layerDeg B F) := by
  intro i hi
  rw [eq_bot_iff]
  refine iSup_le fun m => iSup_le fun p => iSup_le fun h => ?_
  subst h
  exact absurd ⟨⟨p, by simp; ring⟩, rfl⟩ hi

theorem trivialDeg_evenZero {𝒱 : Type*} [AddCommGroup 𝒱] [Module ℂ 𝒱]
    (W : VOA.VertexOperatorAlgebra 𝒱) : EvenZero (trivialDeg W) := by
  intro i hi
  unfold trivialDeg
  rw [if_neg]
  intro h
  apply hi
  rw [h]
  exact ⟨⟨0, rfl⟩, rfl⟩

theorem matterDeg_evenZero : EvenZero matterDeg :=
  tensorDeg_evenZero (tensorDeg_evenZero (layerDeg_evenZero _ _) (trivialDeg_evenZero _))
    (layerDeg_evenZero _ _)

/-! ### Relative states at odd `2R` and ghost number zero -/

theorem antighostZero_eq_lTensor (a : Fin 3) :
    antighostZero matterSVA a = (gMode a 0 0).lTensor MatterSpace := by
  apply TensorProduct.ext'; intro x y
  rw [antighostZero_tmul a (matter_mem_parity_zero x), koszul_zero_right, one_smul,
    LinearMap.lTensor_tmul]
  rfl

theorem lTensor_parity_fix {x : BRSTSpace}
    (hx : x ∈ relativeCarrier leeYangMatterAction.toAffineSl2Action) (a : Fin 3)
    (P : Module.End ℂ Sl2GhostSpace)
    (hP : P = LinearMap.id - (2 : ℂ) • (gMode a 1 (-1) * gMode a 0 0)) :
    P.lTensor MatterSpace x = x := by
  have h0 : (gMode a 0 0).lTensor MatterSpace x = 0 := by
    rw [← antighostZero_eq_lTensor]
    exact ((mem_relativeCarrier _ x).mp hx).2 a
  rw [hP, LinearMap.lTensor_sub, LinearMap.lTensor_smul, LinearMap.lTensor_mul,
    LinearMap.sub_apply, LinearMap.smul_apply, Module.End.mul_apply, h0, map_zero, smul_zero,
    sub_zero, LinearMap.lTensor_id, LinearMap.id_apply]

/-- Relative states are fixed by the product of the three `c₀`-parities. -/
theorem ghostParity_relative {x : BRSTSpace}
    (hx : x ∈ relativeCarrier leeYangMatterAction.toAffineSl2Action) :
    ghostParity.lTensor MatterSpace x = x := by
  rw [ghostParity_eq, LinearMap.lTensor_mul, LinearMap.lTensor_mul, Module.End.mul_apply,
    Module.End.mul_apply, lTensor_parity_fix hx 2 _ parity_two_eq,
    lTensor_parity_fix hx 1 _ parity_one_eq, lTensor_parity_fix hx 0 _ parity_zero_eq]

/-- On a BRST piece of odd `2R` at ghost number zero, the parity is `-1`. -/
theorem ghostParity_odd (j : ℤ) (hj : ¬ Even j) (w : ℂ) (x : BRSTSpace)
    (hx : x ∈ tensorDeg matterDeg ghostDeg ((j, 0), w)) :
    ghostParity.lTensor MatterSpace x = -x := by
  refine tensorDeg_induction matterDeg ghostDeg ((j, 0), w)
    (fun z => ghostParity.lTensor MatterSpace z = -z) (by simp)
    (fun x y hx hy => by beta_reduce at hx hy ⊢; rw [map_add, hx, hy, neg_add])
    (fun c x hx => by beta_reduce at hx ⊢; rw [map_smul, hx, smul_neg]) ?_ x hx
  intro b m hm y hy
  by_cases hb : Even b.1.1 ∧ b.1.2 = 0
  · rw [LinearMap.lTensor_tmul, ghostParity_ghostDeg _ y hy, TensorProduct.tmul_smul,
      ← TensorProduct.tmul_neg, ← neg_one_smul ℂ y, TensorProduct.tmul_smul]
    congr 1
    unfold idxSign psign
    rw [if_neg]
    simp only [Prod.fst_sub, Prod.snd_sub]
    intro he
    apply hj
    have := he.add hb.1
    rw [hb.2] at this
    simpa using this
  · rw [matterDeg_evenZero b hb, Submodule.mem_bot] at hm
    rw [hm, TensorProduct.zero_tmul, map_zero, neg_zero]

/-- **The interpreted piece of the relative complex at `(2p+1, 0)` is zero**, for every
standard ghost grading. -/
theorem relDeg_odd_eq_bot {PG : SesqForm Sl2GhostSpace} (Gh : GhostRGrading PG) (hs : Gh.IsStd)
    (n : ℤ) (p : ℕ) : relDeg Gh n (2 * (p : ℤ) + 1, 0) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hx' : (x : BRSTSpace) ∈ tensorDeg matterDeg ghostDeg ((2 * (p : ℤ) + 1, 0), (n : ℂ)) := by
    have := hx
    change (x : BRSTSpace) ∈ brstDeg Gh _ at this
    rwa [brstDeg, hs] at this
  have h1 := ghostParity_relative (inf_le_left (a := relativeCarrier _) x.2)
  have h2 := ghostParity_odd (2 * (p : ℤ) + 1) (by
    rw [Int.not_even_iff_odd]; exact ⟨p, rfl⟩) _ _ hx'
  rw [h1] at h2
  have h4 : (x : BRSTSpace) = 0 := by
    have h3 : (2 : ℂ) • (x : BRSTSpace) = 0 := by rw [two_smul]; nth_rewrite 1 [h2]; simp
    exact (smul_eq_zero.mp h3).resolve_left two_ne_zero
  exact (Submodule.mem_bot _).mpr (Subtype.ext h4)

end

end VOA.ConcreteHodge

namespace VOA.CyclicEval

open VOA.ConcreteHodge VOA.GradedUnitaryCohomology VOA.LeeYangTransferAssembly
open Module (finrank)

set_option synthInstance.maxHeartbeats 200000

/-- **The endpoint has no leading cohomology at odd `2R`** (the `odd_zero` field of
`LeadingCyclicEvaluation`), proved. -/
theorem endpoint_oddZero (hA : GradedUnitary affineForm affineRealStructure affineFlag) :
    ∀ n (hp : IsPosOn ((endpointKahler hA).geometry n).P ⊤) (p : ℕ),
      finrank ℂ (((endpointKahler hA).model n hp).leadCohom (2 * (p : ℤ) + 1, 0)) = 0 := by
  intro n hp p
  exact finrank_leadCohom_eq_zero_of_deg ((endpointKahler hA).model n hp) _
    (relDeg_odd_eq_bot bgGh bgGh_isStd n p)

end VOA.CyclicEval
