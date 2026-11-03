/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.AffineSl2BelowCriticalGradedUnitarity
import VOA.Examples.AffineSl2CurrentRealization

/-!
# The compact real structure on `V^k(sl₂)` at real level

For real `k` with `k + 2 ≠ 0` this file **constructs** a real structure on the universal affine
VOA `V^k(sl₂)` and proves it is compact (`IsCompactRealStructure`).

Construction.

1. `ConjMod k` is the vacuum module with the complex-conjugate scalar action.  The current modes
   `J^a_m` are still `ℂ`-linear on it, and because the structure constants of `sl₂` and the level
   are real they satisfy the level-`k` affine relations there (`conjCurrentData`).  The universal
   property of the vacuum module (`VacuumCurrentRealization.eval`) therefore gives a `ℂ`-linear map
   `V^k → ConjMod k`, i.e. an **anti-linear** map `basisConj : V^k → V^k` fixing the vacuum and
   commuting with every current mode.
2. `compactRho = vacuumChevalley ∘ basisConj` sends `J^a_m` to `-J^{a*}_m` and fixes the vacuum.
3. Covariance propagates through derivatives and normal-ordered products to every word field
   `YwordA`, hence to the whole state–field map, and to the Sugawara field; `ρ² = 1`.

Main results (unconditional, for real `k`):

* `compactRealStructure k hreal hk : RealStructure (universal k hk)`;
* `compactRealStructure_isCompact` — it is compact;
* `compactRealFamily` — the family over real `x < -2`;
* `universal_gradedUnitary_belowCritical_compact` — the assembled below-critical theorem for this
  family, conditional only on `LayerSignAnchor` and `LayerSignRigidity`.
-/

namespace VOA

namespace AffineSl2BelowCritical

open AffineVOA AffineVOA.Inst AffineLie AffineSl2GeneralRigidity AffineVOA.HighestModule
open Module (End)

noncomputable section

/-! ## The conjugate vacuum module -/

/-- The vacuum module with the complex-conjugate scalar action. -/
def ConjMod (k : ℂ) : Type := WakModule k

instance (k : ℂ) : AddCommGroup (ConjMod k) := inferInstanceAs (AddCommGroup (WakModule k))

instance (k : ℂ) : Module ℂ (ConjMod k) :=
  Module.compHom (WakModule k) (starRingEnd ℂ)

variable {k : ℂ}

/-- Identity into the conjugate module. -/
def toConj (x : WakModule k) : ConjMod k := x

/-- Identity out of the conjugate module. -/
def ofConj (x : ConjMod k) : WakModule k := x

@[simp] theorem ofConj_toConj (x : WakModule k) : ofConj (toConj x) = x := rfl
@[simp] theorem toConj_ofConj (x : ConjMod k) : toConj (ofConj x) = x := rfl
@[simp] theorem ofConj_add (x y : ConjMod k) : ofConj (x + y) = ofConj x + ofConj y := rfl
@[simp] theorem ofConj_zero : ofConj (0 : ConjMod k) = 0 := rfl
theorem ofConj_smul (c : ℂ) (x : ConjMod k) :
    ofConj (c • x) = (starRingEnd ℂ) c • ofConj x := rfl

/-- An operator on the vacuum module, viewed on the conjugate module. -/
def conjEnd (A : End ℂ (WakModule k)) : End ℂ (ConjMod k) where
  toFun x := toConj (A (ofConj x))
  map_add' x y := by simp only [ofConj_add, map_add]; rfl
  map_smul' c x := by
    change toConj (A ((starRingEnd ℂ) c • ofConj x)) = _
    rw [map_smul]
    rfl

@[simp] theorem ofConj_conjEnd (A : End ℂ (WakModule k)) (x : ConjMod k) :
    ofConj (conjEnd A x) = A (ofConj x) := rfl

theorem conjEnd_mul (A B : End ℂ (WakModule k)) : conjEnd (A * B) = conjEnd A * conjEnd B := rfl

theorem conjEnd_add (A B : End ℂ (WakModule k)) : conjEnd (A + B) = conjEnd A + conjEnd B := rfl

theorem conjEnd_sub (A B : End ℂ (WakModule k)) : conjEnd (A - B) = conjEnd A - conjEnd B := rfl

theorem conjEnd_zero : conjEnd (0 : End ℂ (WakModule k)) = 0 := rfl

theorem conjEnd_smul (c : ℂ) (A : End ℂ (WakModule k)) :
    conjEnd (c • A) = (starRingEnd ℂ) c • conjEnd A := by
  apply LinearMap.ext
  intro x
  change toConj (c • A (ofConj x)) = _
  change _ = toConj ((starRingEnd ℂ) ((starRingEnd ℂ) c) • A (ofConj x))
  rw [Complex.conj_conj]

theorem conjEnd_one : conjEnd (1 : End ℂ (WakModule k)) = 1 := rfl

theorem conjEnd_lie (A B : End ℂ (WakModule k)) :
    conjEnd ⁅A, B⁆ = ⁅conjEnd A, conjEnd B⁆ := by
  rw [Ring.lie_def, Ring.lie_def, conjEnd_sub, conjEnd_mul, conjEnd_mul]

/-! ## Coordinatewise conjugation on `sl₂` -/

/-- Coordinatewise complex conjugation of a Chevalley-coordinate vector. -/
def starSl2 (x : Sl2) : Sl2 := fun a => (starRingEnd ℂ) (x a)

theorem starSl2_add (x y : Sl2) : starSl2 (x + y) = starSl2 x + starSl2 y := by
  funext a; simp [starSl2]

theorem starSl2_smul (c : ℂ) (x : Sl2) :
    starSl2 (c • x) = (starRingEnd ℂ) c • starSl2 x := by
  funext a; simp [starSl2]

theorem fabc_real (a b c : Fin 3) : (starRingEnd ℂ) (fabc a b c) = fabc a b c := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> simp [fabc, map_ofNat]

theorem kappa_real (a b : Fin 3) : (starRingEnd ℂ) (kappa a b) = kappa a b := by
  fin_cases a <;> fin_cases b <;> simp [kappa, map_ofNat]

theorem starSl2_lie (x y : Sl2) : starSl2 ⁅x, y⁆ = ⁅starSl2 x, starSl2 y⁆ := by
  funext c
  simp only [starSl2, bracket_apply, map_sum, map_mul, fabc_real]

theorem kappaForm_starSl2 (x y : Sl2) :
    kappaForm (starSl2 x) (starSl2 y) = (starRingEnd ℂ) (kappaForm x y) := by
  simp only [kappaForm_apply, starSl2, map_sum, map_mul, kappa_real]

theorem starSl2_basis (a : Fin 3) : starSl2 (basis a) = basis a := by
  funext b
  simp only [starSl2, basis, Pi.single_apply]
  split_ifs <;> simp

/-! ## The conjugate current data -/

/-- The conjugated loop modes on the conjugate module. -/
def conjLoop (k : ℂ) (n : ℤ) : Sl2 →ₗ[ℂ] End ℂ (ConjMod k) where
  toFun x := conjEnd (vacuumRho kappaForm kappaForm_isInvariant k
    (ofLoop kappaForm kappaForm_isInvariant (starSl2 x) n))
  map_add' x y := by
    rw [starSl2_add, ← ofLoopₗ_apply, map_add, map_add, conjEnd_add]
    rfl
  map_smul' c x := by
    rw [starSl2_smul, ← ofLoopₗ_apply, map_smul, map_smul, conjEnd_smul, Complex.conj_conj]
    rfl

theorem conjLoop_apply (n : ℤ) (x : Sl2) :
    conjLoop k n x = conjEnd (vacuumRho kappaForm kappaForm_isInvariant k
      (ofLoop kappaForm kappaForm_isInvariant (starSl2 x) n)) := rfl

/-- At a real level the conjugated currents satisfy the level-`k` affine relations. -/
def conjCurrentData (k : ℂ) (hreal : (starRingEnd ℂ) k = k) : AffineCurrentData k (ConjMod k) where
  loopMode := conjLoop k
  degree := conjEnd (vacuumRho kappaForm kappaForm_isInvariant k
    (ell0 kappaForm kappaForm_isInvariant))
  vacuum := toConj (vacuumVector kappaForm kappaForm_isInvariant k)
  loop_comm x y m n := by
    rw [conjLoop_apply, conjLoop_apply, ← conjEnd_lie,
      ← (vacuumRho kappaForm kappaForm_isInvariant k).map_lie, affine_bracket, map_add,
      conjEnd_add, ← starSl2_lie, kappaForm_starSl2, conjLoop_apply]
    congr 1
    split_ifs
    · rw [map_smul, vacuum_acts_central, conjEnd_smul, conjEnd_smul,
        show conjEnd (LinearMap.id : End ℂ (WakModule k)) = 1 from rfl, smul_smul, smul_smul]
      congr 1
      simp only [map_mul, Complex.conj_conj, map_intCast, hreal]
    · rw [map_zero, conjEnd_zero]
  degree_comm x n := by
    rw [conjLoop_apply, ← conjEnd_lie, ← (vacuumRho kappaForm kappaForm_isInvariant k).map_lie,
      ell0_lie_ofLoop, map_smul, conjEnd_smul, map_intCast]
  pos_annihilate x n hn := by
    rw [conjLoop_apply]
    change toConj (vacuumRho kappaForm kappaForm_isInvariant k
      (ofLoop kappaForm kappaForm_isInvariant (starSl2 x) n)
        (vacuumVector kappaForm kappaForm_isInvariant k)) = 0
    rw [vacuum_pos_annihilate _ _ _ _ _ hn]
    rfl
  degree_vacuum := by
    change toConj (vacuumRho kappaForm kappaForm_isInvariant k
      (ell0 kappaForm kappaForm_isInvariant) (vacuumVector kappaForm kappaForm_isInvariant k)) = 0
    rw [vacuum_ell0_annihilate]
    rfl

/-! ## The PBW conjugation -/

variable (hreal : (starRingEnd ℂ) k = k)

/-- The universal evaluation into the conjugate module. -/
def basisConjₗ : WakModule k →ₗ[ℂ] ConjMod k :=
  (conjCurrentData k hreal).toVacuumCurrentRealization.eval

/-- **The anti-linear PBW conjugation** on `V^k(sl₂)` at real `k`. -/
def basisConj (x : WakModule k) : WakModule k := ofConj (basisConjₗ hreal x)

theorem basisConj_add (x y : WakModule k) :
    basisConj hreal (x + y) = basisConj hreal x + basisConj hreal y := by
  simp only [basisConj, map_add, ofConj_add]

theorem basisConj_smul (c : ℂ) (x : WakModule k) :
    basisConj hreal (c • x) = (starRingEnd ℂ) c • basisConj hreal x := by
  simp only [basisConj, map_smul, ofConj_smul]

theorem basisConj_vacuum : basisConj hreal (vacuumA k) = vacuumA k := by
  simp only [basisConj, basisConjₗ, vacuumA, VacuumCurrentRealization.eval_vacuum]
  rfl

/-- The PBW conjugation commutes with every current mode. -/
theorem basisConj_J (a : Fin 3) (n : ℤ) (v : WakModule k) :
    basisConj hreal (J k a n v) = J k a n (basisConj hreal v) := by
  simp only [basisConj, basisConjₗ, VacuumCurrentRealization.eval_J,
    AffineCurrentData.toVacuumCurrentRealization_current]
  change ofConj (conjLoop k n (basis a) _) = _
  rw [conjLoop_apply, ofConj_conjEnd, starSl2_basis, J_eq]

/-! ## The compact conjugation -/

/-- **The compact conjugation** `ρ = θ ∘ basisConj`, `θ = vacuumChevalley`. -/
def compactRho : WakModule k →+ WakModule k where
  toFun x := vacuumChevalley k (basisConj hreal x)
  map_zero' := by
    have h := basisConj_smul hreal 0 0
    simp only [zero_smul, map_zero] at h
    rw [h, map_zero]
  map_add' x y := by rw [basisConj_add, map_add]

theorem compactRho_apply (x : WakModule k) :
    compactRho hreal x = vacuumChevalley k (basisConj hreal x) := rfl

theorem compactRho_smul (c : ℂ) (x : WakModule k) :
    compactRho hreal (c • x) = (starRingEnd ℂ) c • compactRho hreal x := by
  rw [compactRho_apply, basisConj_smul, map_smul]; rfl

theorem compactRho_vacuum : compactRho hreal (vacuumA k) = vacuumA k := by
  rw [compactRho_apply, basisConj_vacuum, vacuumChevalley_vacuum]

theorem compactRho_J (a : Fin 3) (n : ℤ) (v : WakModule k) :
    compactRho hreal (J k a n v) = -J k (adjointColour a) n (compactRho hreal v) := by
  rw [compactRho_apply, basisConj_J, vacuumChevalley_current]; rfl

/-- The flipped creation word. -/
def flipWord (w : List (Fin 3 × ℕ)) : List (Fin 3 × ℕ) :=
  w.map (fun an => (adjointColour an.1, an.2))

theorem compactRho_wordStateA (w : List (Fin 3 × ℕ)) :
    compactRho hreal (wordStateA k w) = ((-1 : ℂ) ^ w.length) • wordStateA k (flipWord w) := by
  induction w with
  | nil => simp [flipWord, compactRho_vacuum]
  | cons b w ih =>
      rw [wordStateA_cons, compactRho_J, ih, map_smul]
      simp only [flipWord, List.map_cons, wordStateA_cons, List.length_cons, pow_succ]
      rw [mul_neg_one, neg_smul]

/-- `ρ² = 1`. -/
theorem compactRho_compactRho (x : WakModule k) : compactRho hreal (compactRho hreal x) = x := by
  have hw : ∀ w : List (Fin 3 × ℕ),
      compactRho hreal (compactRho hreal (wordStateA k w)) = wordStateA k w := by
    intro w
    induction w with
    | nil => rw [wordStateA_nil, compactRho_vacuum, compactRho_vacuum]
    | cons b w ih =>
        rw [wordStateA_cons, compactRho_J, map_neg, compactRho_J, neg_neg,
          adjointColour_involutive, ih]
  have hx : x ∈ Submodule.span ℂ (Set.range (wordStateA k)) := by
    rw [wordStateA_span]; trivial
  induction hx using Submodule.span_induction with
  | mem z hz => obtain ⟨w, rfl⟩ := hz; exact hw w
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, map_add, hx, hy]
  | smul c x _ hx => rw [compactRho_smul, compactRho_smul, Complex.conj_conj, hx]

/-! ## Field covariance -/

/-- Covariance of an additive map with a pair of fields, up to a sign. -/
def FieldCov (φ : WakModule k →+ WakModule k) (s : ℂ)
    (a a' : FormalDist (End ℂ (WakModule k))) : Prop :=
  ∀ (j : ℤ) (v : WakModule k), φ (a j v) = s • a' j (φ v)

variable {hreal}

theorem FieldCov.nprod {s t : ℂ} {a a' b b' : FormalDist (End ℂ (WakModule k))}
    (ha : IsField a) (ha' : IsField a') (hb : IsField b) (hb' : IsField b')
    (hca : FieldCov (compactRho hreal) s a a') (hcb : FieldCov (compactRho hreal) t b b') :
    FieldCov (compactRho hreal) (s * t) (VOA.nprod ha hb) (VOA.nprod ha' hb') := by
  intro j v
  rw [nprod_apply, nprod_apply, map_finsum (compactRho hreal)
    (normalOrdered_diag_support_finite ha hb j v),
    smul_finsum' (s * t) (normalOrdered_diag_support_finite ha' hb' j _)]
  refine finsum_congr fun m => ?_
  rw [normalOrdered_apply, normalOrdered_apply]
  split_ifs
  · rw [Module.End.mul_apply, Module.End.mul_apply, hca, hcb, map_smul, smul_smul]
  · rw [Module.End.mul_apply, Module.End.mul_apply, hcb, hca, map_smul, smul_smul, mul_comm]

theorem FieldCov.deriv {s : ℂ} {a a' : FormalDist (End ℂ (WakModule k))}
    (ha : FieldCov (compactRho hreal) s a a') :
    FieldCov (compactRho hreal) s (VOA.deriv a) (VOA.deriv a') := by
  intro j v
  rw [deriv_apply, deriv_apply]
  change compactRho hreal ((j + 1) • a (j + 1) v) = s • ((j + 1) • a' (j + 1) _)
  rw [map_zsmul, ha, smul_comm]

theorem FieldCov.deriv_iterate {s : ℂ} {a a' : FormalDist (End ℂ (WakModule k))}
    (ha : FieldCov (compactRho hreal) s a a') :
    ∀ i : ℕ, FieldCov (compactRho hreal) s (VOA.deriv^[i] a) (VOA.deriv^[i] a')
  | 0 => ha
  | i + 1 => by
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact (ha.deriv_iterate i).deriv

theorem FieldCov.smul_real {s r : ℂ} (hr : (starRingEnd ℂ) r = r)
    {a a' : FormalDist (End ℂ (WakModule k))} (ha : FieldCov (compactRho hreal) s a a') :
    FieldCov (compactRho hreal) s (r • a) (r • a') := by
  intro j v
  change compactRho hreal (r • a j v) = s • (r • a' j _)
  rw [compactRho_smul, hr, ha, smul_comm]

theorem fieldCov_Jfield (a : Fin 3) :
    FieldCov (compactRho hreal) (-1) (Jfield k a) (Jfield k (adjointColour a)) := by
  intro j v
  rw [Jfield_apply, Jfield_apply, compactRho_J, neg_one_smul]

theorem fieldCov_genFieldA (a : Fin 3) (i : ℕ) :
    FieldCov (compactRho hreal) (-1) (genFieldA k a i) (genFieldA k (adjointColour a) i) := by
  unfold genFieldA
  refine FieldCov.smul_real ?_ ((fieldCov_Jfield a).deriv_iterate i)
  simp only [map_inv₀, map_natCast]

theorem fieldCov_idFieldA :
    FieldCov (compactRho hreal) 1 (idFieldA k) (idFieldA k) := by
  intro j v
  rw [one_smul, idFieldA]
  split_ifs
  · rfl
  · simp

theorem fieldCov_YwordA : ∀ w : List (Fin 3 × ℕ),
    FieldCov (compactRho hreal) ((-1 : ℂ) ^ w.length) (YwordA k w) (YwordA k (flipWord w))
  | [] => by simpa using fieldCov_idFieldA
  | b :: w => by
      rw [YwordA_cons]
      have h := FieldCov.nprod (genFieldA_isField k b.1 b.2)
        (genFieldA_isField k (adjointColour b.1) b.2) (YwordA_isField k w)
        (YwordA_isField k (flipWord w)) (fieldCov_genFieldA b.1 b.2) (fieldCov_YwordA w)
      have hflip : flipWord (b :: w) = (adjointColour b.1, b.2) :: flipWord w := rfl
      rw [hflip, YwordA_cons]
      convert h using 1
      simp only [List.length_cons, pow_succ]
      ring

variable (hreal) (hk : k + 2 ≠ 0)

/-- **Covariance of the whole state–field map**: `ρ(Y(u)_j v) = Y(ρu)_j (ρ v)`. -/
theorem compactRho_YA (u : WakModule k) (j : ℤ) (v : WakModule k) :
    compactRho hreal (YA k hk u j v) = YA k hk (compactRho hreal u) j (compactRho hreal v) := by
  have hu : u ∈ Submodule.span ℂ (Set.range (wordStateA k)) := by
    rw [wordStateA_span]; trivial
  induction hu using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨w, rfl⟩ := hz
      rw [YA_wordState, compactRho_wordStateA, map_smul, YA_wordState]
      exact fieldCov_YwordA w j v
  | zero => simp
  | add x y _ _ hx hy =>
      simp only [map_add]
      change compactRho hreal (YA k hk x j v + YA k hk y j v) =
        YA k hk (compactRho hreal x) j _ + YA k hk (compactRho hreal y) j _
      rw [map_add, hx, hy]
  | smul c x _ hx =>
      rw [compactRho_smul, map_smul, map_smul]
      change compactRho hreal (c • YA k hk x j v) = (starRingEnd ℂ) c • YA k hk _ j _
      rw [compactRho_smul, hx]

theorem dist_smul_apply (r : ℂ) (a : FormalDist (End ℂ (WakModule k))) (j : ℤ) :
    (r • a) j = r • a j := rfl

theorem dist_sum_apply {ι : Type*} (s : Finset ι) (F : ι → FormalDist (End ℂ (WakModule k)))
    (j : ℤ) : (∑ i ∈ s, F i) j = ∑ i ∈ s, F i j := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, ← ih]
      rfl

theorem adjointColour_zero' : adjointColour 0 = 1 := rfl
theorem adjointColour_one' : adjointColour 1 = 0 := rfl
theorem adjointColour_two' : adjointColour 2 = 2 := rfl

/-- Covariance of the Sugawara field. -/
theorem compactRho_sugawara (j : ℤ) (v : WakModule k) :
    compactRho hreal (VOA.AffineVOA.sugawaraField k j v) =
      VOA.AffineVOA.sugawaraField k j (compactRho hreal v) := by
  have hpair : ∀ a b : Fin 3, ∀ j v,
      compactRho hreal (nprod (Jfield_isField k a) (Jfield_isField k b) j v) =
        nprod (Jfield_isField k (adjointColour a)) (Jfield_isField k (adjointColour b)) j
          (compactRho hreal v) := by
    intro a b j v
    have h := FieldCov.nprod (Jfield_isField k a) (Jfield_isField k (adjointColour a))
      (Jfield_isField k b) (Jfield_isField k (adjointColour b))
      (fieldCov_Jfield (hreal := hreal) a) (fieldCov_Jfield (hreal := hreal) b) j v
    rw [h]
    norm_num
  have hc : (starRingEnd ℂ) ((2 * (k + dualCoxeter))⁻¹) = (2 * (k + dualCoxeter))⁻¹ := by
    simp [dualCoxeter, hreal, map_ofNat]
  have hki : ∀ a b : Fin 3, (starRingEnd ℂ) (kappaInv a b) = kappaInv a b := by
    intro a b; fin_cases a <;> fin_cases b <;> simp [kappaInv, map_ofNat]
  have hsug : ∀ (j' : ℤ) (v' : WakModule k), VOA.AffineVOA.sugawaraField k j' v' =
      (2 * (k + dualCoxeter))⁻¹ • ∑ a : Fin 3, ∑ b : Fin 3,
        kappaInv a b • nprod (Jfield_isField k a) (Jfield_isField k b) j' v' := by
    intro j' v'
    rw [VOA.AffineVOA.sugawaraField, dist_smul_apply, LinearMap.smul_apply, dist_sum_apply,
      LinearMap.sum_apply]
    congr 1
  rw [hsug, hsug, compactRho_smul, hc, map_sum]
  congr 1
  simp only [map_sum, compactRho_smul, hki, hpair]
  simp only [Fin.sum_univ_three, kappaInv, adjointColour_zero', adjointColour_one',
    adjointColour_two']
  norm_num
  abel

/-- **The compact real structure** on `V^k(sl₂)` at real `k`. -/
def compactRealStructure : RealStructure (universal k hk) where
  rho := compactRho hreal
  antilinear := compactRho_smul hreal
  map_smul u n v := by
    change compactRho hreal (mode (YA k hk u) n v) =
      mode (YA k hk (compactRho hreal u)) n (compactRho hreal v)
    rw [mode_apply, mode_apply, compactRho_YA]
  map_vacuum := compactRho_vacuum hreal
  map_omega := by
    change compactRho hreal (omegaA k) = omegaA k
    rw [VOA.AffineVOA.omegaA_eq, compactRho_sugawara, compactRho_vacuum]
  parity := fun _ => 1
  sq := by
    intro h v _
    rw [one_smul]
    exact compactRho_compactRho hreal v

/-- The constructed real structure is compact. -/
theorem compactRealStructure_isCompact :
    IsCompactRealStructure (compactRealStructure hreal hk) where
  current a := by
    change compactRho hreal (currentState k a) = _
    rw [currentState_def, compactRho_J, compactRho_vacuum, currentState_def]
  parity_ne_zero _ := one_ne_zero

/-- Real levels are fixed by complex conjugation. -/
theorem conj_ofReal (x : ℝ) : (starRingEnd ℂ) (x : ℂ) = x := Complex.conj_ofReal x

/-- **The compact family over the real interval `(-∞, -2)`.** -/
def compactRealFamily : RealFamily := fun x hx =>
  compactRealStructure (conj_ofReal x) (noncritical_of_lt hx)

theorem compactRealFamily_isCompact (x : ℝ) (hx : x < -2) :
    IsCompactRealStructure (compactRealFamily x hx) :=
  compactRealStructure_isCompact (conj_ofReal x) (noncritical_of_lt hx)

/-- **Below-critical graded unitarity with the constructed compact real structure.**
For every real `k < -2`, `V^k(sl₂)` with its normalized canonical form, the constructed compact
real structure and the ordinary current-length flag is graded-unitary — conditional only on the
two named analytic inputs `LayerSignAnchor` and `LayerSignRigidity` for this family.

⚠ As stated, conditional on `hanchor` and `hrigid`; both are proved later
(`layerSignAnchor_compact`, `layerSignRigidity_compact`), giving
`universal_gradedUnitary_belowCritical_unconditional`. -/
theorem universal_gradedUnitary_belowCritical_compact
    (hanchor : LayerSignAnchor compactRealFamily) (hrigid : LayerSignRigidity compactRealFamily)
    (k : ℝ) (hk : k < -2) :
    GradedUnitary (universalForm (k : ℂ) (noncritical_of_lt hk)) (compactRealFamily k hk)
      (ordinaryFlag (k : ℂ) (noncritical_of_lt hk)) :=
  universal_gradedUnitary_belowCritical compactRealFamily compactRealFamily_isCompact
    hanchor hrigid k hk

end

end AffineSl2BelowCritical

end VOA
