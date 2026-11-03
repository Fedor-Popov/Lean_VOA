/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneDivisorReduction

/-!
# Type-generic two-slot model, good tables, and the W side

For sector data `S` (generic versions of `A2DivisorPairModel`, `A2DivisorPairGood`, `A2PairW` and
the divisibility part of `A2DivisorFinal`):

* pair tables `Y : Fin n → Fin n → P_m`, the embedding `pemb a b s Y`, and the coadjoint matrices
  `opA`, `opB` (`slotOp_pemb_a`, `slotOp_pemb_b`); `tensor_eq_sum_pemb`: every tensor is the sum of
  the embeddings of its pair tables over canonical spectators (`s a = s b = c₀`);
* `Good a b s`: pair tables whose embedding lies in `P_m M_m`; closed under the pair operators
  (`good_S`, `good_A`) and containing `F · δ_{c₀}⊗δ_{c₀}` with `F = ∏_{j∉{a,b}} D_j^L`
  (`good_base`); `factor_dvd`: `H^D F ∣ E_{ab}^{2D + L m}`;
* **W side** (`x ∈ W_m`): `anti_dvd` (`z_a - z_b ∣ Y c d - Y d c`) and `relSym_sq_dvd`
  (`(z_a - z_b)² ∣ Σ_{c,d} M_r(c,d) (Y c d + Y d c)`), from swap symmetry and the current equations.
-/

namespace VOA.DeligneAudit.DeligneDivisor

open MvPolynomial VOA.DeligneAudit.SectorLoop VOA.DeligneAudit.SectorFiber
open VOA.DeligneAudit.SectorFiberModule VOA.QuadraticCurrentFunctionalCarrier
open VOA.QuadraticJetCoefficientPairing VOA.CollisionCommonFactors VOA.DeligneAuxiliaryCollision
open VOA.DeligneAudit.DeligneSector
open VOA.DeligneAudit.A2 (Pm pairE Gpair Dslot Gpair_a_dvd Gpair_b_dvd Dslot_dvd ia ia_ne swap_swap)

noncomputable section

variable {S : DeligneSectorData} {m : ℕ}

variable (S) in
/-- Two-slot tables with polynomial entries. -/
abbrev PairTable (m : ℕ) := Fin S.n → Fin S.n → Pm m

/-- The labelling `s[a↦c][b↦d]`. -/
def pairLabel (a b : Fin m) (s : Fin m → Fin S.n) (c d : Fin S.n) : Fin m → Fin S.n :=
  Function.update (Function.update s a c) b d

/-- The pair table of a tensor. -/
def pairTable (x : TPs S m) (a b : Fin m) (s : Fin m → Fin S.n) : PairTable S m :=
  fun c d => x (pairLabel a b s c d)

/-- Embedding a pair table. -/
def pemb (a b : Fin m) (s : Fin m → Fin S.n) (Y : PairTable S m) : TPs S m :=
  ∑ c, ∑ d, Y c d • deltaT (pairLabel a b s c d)

/-- Coadjoint action in the first slot. -/
def opA (x : Fin S.n) (Y : PairTable S m) : PairTable S m :=
  fun c d => -∑ e, MvPolynomial.C (S.f x c e) * Y e d

/-- Coadjoint action in the second slot. -/
def opB (x : Fin S.n) (Y : PairTable S m) : PairTable S m :=
  fun c d => -∑ e, MvPolynomial.C (S.f x d e) * Y c e

/-- Agreement off the two slots. -/
def AgreeOff (a b : Fin m) (s t : Fin m → Fin S.n) : Prop := ∀ k, k ≠ a → k ≠ b → t k = s k

instance (a b : Fin m) (s t : Fin m → Fin S.n) : Decidable (AgreeOff a b s t) := by
  unfold AgreeOff; infer_instance

theorem pairLabel_eq_iff (a b : Fin m) (hab : a ≠ b) (s t : Fin m → Fin S.n) (c d : Fin S.n) :
    t = pairLabel a b s c d ↔ AgreeOff a b s t ∧ t a = c ∧ t b = d := by
  constructor
  · rintro rfl
    refine ⟨fun k hka hkb => ?_, ?_, ?_⟩
    · simp [pairLabel, Function.update_of_ne hka, Function.update_of_ne hkb]
    · simp [pairLabel, Function.update_of_ne hab]
    · simp [pairLabel]
  · rintro ⟨h, rfl, rfl⟩
    funext k
    by_cases hkb : k = b
    · subst hkb; simp [pairLabel]
    · by_cases hka : k = a
      · subst hka; simp [pairLabel, Function.update_of_ne hkb]
      · simp [pairLabel, Function.update_of_ne hka, Function.update_of_ne hkb, h k hka hkb]

theorem pemb_apply (a b : Fin m) (hab : a ≠ b) (s : Fin m → Fin S.n) (Y : PairTable S m)
    (t : Fin m → Fin S.n) :
    pemb a b s Y t = if AgreeOff a b s t then Y (t a) (t b) else 0 := by
  classical
  simp only [pemb, Finset.sum_apply, psmul_apply, deltaT, mul_ite, mul_one, mul_zero,
    pairLabel_eq_iff a b hab]
  by_cases h : AgreeOff a b s t
  · simp only [h, true_and]
    rw [Finset.sum_eq_single (t a)]
    · rw [Finset.sum_eq_single (t b)]
      · simp
      · intro d _ hd; simp [Ne.symm hd]
      · simp
    · intro c _ hc
      refine Finset.sum_eq_zero fun d _ => ?_
      simp [Ne.symm hc]
    · simp
  · simp [h]

theorem agreeOff_update_a (a b : Fin m) (s t : Fin m → Fin S.n) (e : Fin S.n) :
    AgreeOff a b s (Function.update t a e) ↔ AgreeOff a b s t := by
  unfold AgreeOff
  refine forall_congr' fun k => ?_
  constructor
  · intro h hka hkb; have := h hka hkb; rwa [Function.update_of_ne hka] at this
  · intro h hka hkb; rw [Function.update_of_ne hka]; exact h hka hkb

theorem agreeOff_update_b (a b : Fin m) (s t : Fin m → Fin S.n) (e : Fin S.n) :
    AgreeOff a b s (Function.update t b e) ↔ AgreeOff a b s t := by
  unfold AgreeOff
  refine forall_congr' fun k => ?_
  constructor
  · intro h hka hkb; have := h hka hkb; rwa [Function.update_of_ne hkb] at this
  · intro h hka hkb; rw [Function.update_of_ne hkb]; exact h hka hkb

/-- **Slot `a` acts on pair tables by `opA`.** -/
theorem slotOp_pemb_a (x : Fin S.n) (a b : Fin m) (hab : a ≠ b) (s : Fin m → Fin S.n)
    (Y : PairTable S m) : slotOp x a (pemb a b s Y) = pemb a b s (opA x Y) := by
  funext t
  simp only [slotOp, LinearMap.coe_mk, AddHom.coe_mk]
  rw [pemb_apply a b hab]
  simp only [pemb_apply a b hab, agreeOff_update_a, Function.update_self,
    Function.update_of_ne (Ne.symm hab)]
  by_cases h : AgreeOff a b s t
  · simp only [h, if_true, opA]
  · simp [h]

/-- **Slot `b` acts on pair tables by `opB`.** -/
theorem slotOp_pemb_b (x : Fin S.n) (a b : Fin m) (hab : a ≠ b) (s : Fin m → Fin S.n)
    (Y : PairTable S m) : slotOp x b (pemb a b s Y) = pemb a b s (opB x Y) := by
  funext t
  simp only [slotOp, LinearMap.coe_mk, AddHom.coe_mk]
  rw [pemb_apply a b hab]
  simp only [pemb_apply a b hab, agreeOff_update_b, Function.update_self,
    Function.update_of_ne hab]
  by_cases h : AgreeOff a b s t
  · simp only [h, if_true, opB]
  · simp [h]

theorem pemb_add (a b : Fin m) (s : Fin m → Fin S.n) (Y Z : PairTable S m) :
    pemb a b s (Y + Z) = pemb a b s Y + pemb a b s Z := by
  simp only [pemb, Pi.add_apply, add_smul, Finset.sum_add_distrib]

theorem pemb_smul (a b : Fin m) (s : Fin m → Fin S.n) (p : Pm m) (Y : PairTable S m) :
    pemb a b s (p • Y) = p • pemb a b s Y := by
  simp only [pemb, Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

/-- Canonical spectators: the two slots carry the label `c₀`. -/
def IsCanon (a b : Fin m) (s : Fin m → Fin S.n) : Prop := s a = S.c₀ ∧ s b = S.c₀

instance (a b : Fin m) (s : Fin m → Fin S.n) : Decidable (IsCanon a b s) := by
  unfold IsCanon; infer_instance

/-- **Every tensor is the sum of the embeddings of its pair tables.** -/
theorem tensor_eq_sum_pemb (x : TPs S m) (a b : Fin m) (hab : a ≠ b) :
    x = ∑ s ∈ Finset.univ.filter (IsCanon a b), pemb a b s (pairTable x a b s) := by
  classical
  funext t
  rw [Finset.sum_apply]
  simp only [pemb_apply a b hab]
  set s₀ := pairLabel a b t S.c₀ S.c₀ with hs₀
  have hcan : IsCanon a b s₀ := by
    refine ⟨?_, ?_⟩ <;> simp [s₀, pairLabel, Function.update_of_ne hab]
  have hag : AgreeOff a b s₀ t := by
    intro k hka hkb; simp [s₀, pairLabel, Function.update_of_ne hka, Function.update_of_ne hkb]
  rw [Finset.sum_eq_single s₀]
  · rw [if_pos hag, pairTable]
    congr 1
    exact ((pairLabel_eq_iff a b hab s₀ t (t a) (t b)).mpr ⟨hag, rfl, rfl⟩)
  · intro s hs hne
    rw [Finset.mem_filter] at hs
    rw [if_neg]
    intro hag'
    apply hne
    funext k
    by_cases hka : k = a
    · subst hka; rw [hs.2.1, hcan.1]
    · by_cases hkb : k = b
      · subst hkb; rw [hs.2.2, hcan.2]
      · rw [← hag' k hka hkb, hag k hka hkb]
  · intro h; exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcan⟩) h

/-! ## Good tables -/

theorem opA_smul (x : Fin S.n) (p : Pm m) (Y : PairTable S m) : opA x (p • Y) = p • opA x Y := by
  funext c d
  simp only [opA, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_neg]
  congr 1
  refine Finset.sum_congr rfl fun e _ => ?_
  ring

theorem opB_smul (x : Fin S.n) (p : Pm m) (Y : PairTable S m) : opB x (p • Y) = p • opB x Y := by
  funext c d
  simp only [opB, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_neg]
  congr 1
  refine Finset.sum_congr rfl fun e _ => ?_
  ring

/-- `pemb` as a `P_m`-linear map. -/
def pembL (a b : Fin m) (s : Fin m → Fin S.n) : PairTable S m →ₗ[Pm m] TPs S m where
  toFun := pemb a b s
  map_add' := pemb_add a b s
  map_smul' := pemb_smul a b s

/-- Pair tables whose embedding lies in `P_m M_m`. -/
def Good (a b : Fin m) (s : Fin m → Fin S.n) : Submodule (Pm m) (PairTable S m) :=
  (MP S m).comap (pembL a b s)

/-- `H = G_a G_b`. -/
abbrev Hpair (a b : Fin m) : Pm m := Gpair a b a * Gpair a b b

/-- `z_a - z_b`. -/
abbrev zab (a b : Fin m) : Pm m := zr (K := ℂ) a - zr b

theorem good_S (x : Fin S.n) {a b : Fin m} (hab : a ≠ b) {s : Fin m → Fin S.n}
    {Y : PairTable S m} (hY : Y ∈ Good a b s) : Hpair a b • (opA x Y + opB x Y) ∈ Good a b s := by
  change pemb a b s (Hpair a b • (opA x Y + opB x Y)) ∈ MP S m
  rw [pemb_smul, pemb_add, ← slotOp_pemb_a x a b hab, ← slotOp_pemb_b x a b hab]
  exact pairS_mem x a b hab hY

theorem good_A (x : Fin S.n) {a b : Fin m} (hab : a ≠ b) {s : Fin m → Fin S.n}
    {Y : PairTable S m} (hY : Y ∈ Good a b s) :
    (Hpair a b * zab a b) • (opA x Y - opB x Y) ∈ Good a b s := by
  change pemb a b s ((Hpair a b * zab a b) • (opA x Y - opB x Y)) ∈ MP S m
  have hsub : pemb a b s (opA x Y - opB x Y) = pemb a b s (opA x Y) - pemb a b s (opB x Y) := by
    rw [sub_eq_add_neg, pemb_add, ← neg_one_smul (Pm m) (opB x Y), pemb_smul, neg_one_smul,
      ← sub_eq_add_neg]
  rw [pemb_smul, hsub, ← slotOp_pemb_a x a b hab, ← slotOp_pemb_b x a b hab]
  exact pairA_mem x a b hab hY

variable (S) in
/-- `F = ∏_{j ∉ {a,b}} D_j^L`, `L = S.depth`. -/
def Fspec (a b : Fin m) : Pm m :=
  ∏ j ∈ Finset.univ.filter (fun j => j ≠ a ∧ j ≠ b), Dslot j ^ S.depth

/-- The base table `δ_{c₀} ⊗ δ_{c₀}`. -/
def baseT : PairTable S m := fun c d => if c = S.c₀ ∧ d = S.c₀ then 1 else 0

theorem pemb_baseT {a b : Fin m} (hab : a ≠ b) {s : Fin m → Fin S.n} (hs : IsCanon a b s) :
    pemb a b s (baseT (S := S)) = deltaT s := by
  funext t
  rw [pemb_apply a b hab]
  have hpl : pairLabel a b s S.c₀ S.c₀ = s := by
    funext k
    by_cases hkb : k = b
    · subst hkb; simp [pairLabel, hs.2]
    · by_cases hka : k = a
      · subst hka; simp [pairLabel, Function.update_of_ne hkb, hs.1]
      · simp [pairLabel, Function.update_of_ne hka, Function.update_of_ne hkb]
  have key : t = s ↔ AgreeOff a b s t ∧ t a = S.c₀ ∧ t b = S.c₀ := by
    rw [← pairLabel_eq_iff a b hab s t S.c₀ S.c₀, hpl]
  simp only [deltaT, key, baseT]
  by_cases h : AgreeOff a b s t <;> by_cases h1 : t a = S.c₀ <;> by_cases h2 : t b = S.c₀ <;>
    simp [h, h1, h2]

/-- **Base**: `F · δ_{c₀}⊗δ_{c₀}` is good for canonical spectators. -/
theorem good_base {a b : Fin m} (hab : a ≠ b) {s : Fin m → Fin S.n} (hs : IsCanon a b s) :
    Fspec S a b • baseT (S := S) ∈ Good a b s := by
  change pemb a b s (Fspec S a b • baseT) ∈ MP S m
  rw [pemb_smul, pemb_baseT hab hs, Fspec]
  apply all_slots
  intro j hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and_or, not_not] at hj
  rcases hj with rfl | rfl
  · exact hs.1
  · exact hs.2

/-- **The factor divides a power of `E_{ab}`.** -/
theorem factor_dvd (D : ℕ) (a b : Fin m) (hab : a ≠ b) :
    Hpair a b ^ D * Fspec S a b ∣ pairE (m := m) a b ^ (2 * D + S.depth * m) := by
  rw [pow_add]
  apply mul_dvd_mul
  · rw [Hpair, mul_pow, two_mul, pow_add]
    exact mul_dvd_mul (pow_dvd_pow_of_dvd (Gpair_a_dvd a b hab) D)
      (pow_dvd_pow_of_dvd (Gpair_b_dvd a b hab) D)
  · rw [Fspec]
    refine dvd_trans (Finset.prod_dvd_prod_of_dvd _ (fun _ => pairE (m := m) a b ^ S.depth)
      fun j hj => ?_) ?_
    · simp only [Finset.mem_filter] at hj
      exact pow_dvd_pow_of_dvd (Dslot_dvd a b j hj.2.1 hj.2.2) _
    · rw [Finset.prod_const, ← pow_mul]
      apply pow_dvd_pow
      have := Finset.card_filter_le (Finset.univ : Finset (Fin m)) (fun j => j ≠ a ∧ j ≠ b)
      rw [Finset.card_univ, Fintype.card_fin] at this
      exact Nat.mul_le_mul_left _ this

/-- **From good pair tables to the pair comparison.** -/
theorem pairComparisonG_of_good (D : ℕ)
    (h : ∀ m, ∀ x ∈ currentCarrier S.fullMatrix m 0, ∀ a b : Fin m, a ≠ b →
      ∀ s : Fin m → Fin S.n, IsCanon a b s →
        (Hpair a b ^ D * Fspec S a b) • pairTable x a b s ∈ Good a b s) :
    PairComparisonG S := by
  refine ⟨fun m x hx a b hab => ⟨2 * D + S.depth * m, ?_⟩⟩
  rw [tensor_eq_sum_pemb x a b hab, Finset.smul_sum]
  refine Submodule.sum_mem _ fun s hs => ?_
  have hcan : IsCanon a b s := (Finset.mem_filter.mp hs).2
  obtain ⟨k, hk⟩ := factor_dvd (S := S) (m := m) D a b hab
  have hg := h m x hx a b hab s hcan
  change pemb a b s ((Hpair a b ^ D * Fspec S a b) • pairTable x a b s) ∈ MP S m at hg
  rw [pemb_smul] at hg
  rw [hk, mul_comm, mul_smul]
  exact Submodule.smul_mem _ _ hg

/-! ## The W side -/

section WSide

variable (a b : Fin m) (hab : a ≠ b) (t : Fin m → Fin S.n)

include hab in
theorem update_swap_comp (c d : Fin S.n) :
    Function.update (Function.update t a c) b d ∘ (Equiv.swap a b).symm =
      Function.update (Function.update t a d) b c := by
  funext k
  simp only [Function.comp_apply, Equiv.symm_swap, Function.update_apply, Equiv.swap_apply_def]
  by_cases h1 : k = a
  · subst h1; simp [hab]
  · by_cases h2 : k = b
    · subst h2; simp [Ne.symm hab]; intro h; exact absurd h hab
    · simp [h1, h2]

include hab in
/-- **Swap symmetry of the pair table.** -/
theorem pairTable_swap {x : TPs S m} (hx : x ∈ currentCarrier S.fullMatrix m 0) (c d : Fin S.n) :
    pairTable x a b t d c = swapVariables (ia a) (ia b) (pairTable x a b t c d) := by
  have he : ExtendsCurrentPermutation (Equiv.swap (ia a) (ia b)) (Equiv.swap a b) := fun k =>
    (Fin.castAdd_injective m 0).swap_apply _ _ _
  have h := hx.1 _ _ he (Function.update (Function.update t a c) b d)
  rw [update_swap_comp a b hab] at h
  exact h.symm

include hab in
/-- **The antisymmetric part of a carrier pair table is divisible by `z_a - z_b`.** -/
theorem anti_dvd {x : TPs S m} (hx : x ∈ currentCarrier S.fullMatrix m 0) (c d : Fin S.n) :
    zab a b ∣ pairTable x a b t c d - pairTable x a b t d c := by
  rw [pairTable_swap a b hab t hx c d]
  exact collisionFactor_dvd_sub_swapVariables (ia a) (ia b) (ia_ne a b hab) _

/-- The unsymmetrized pairing with a relation. -/
def relF (r : Option S.ρ) (Y : PairTable S m) : Pm m :=
  ∑ c, ∑ d, MvPolynomial.C (S.fullMatrix r (c, d)) * Y c d

/-- The symmetrized pairing with a relation. -/
def relSym (r : Option S.ρ) (Y : PairTable S m) : Pm m :=
  ∑ c, ∑ d, MvPolynomial.C (S.fullMatrix r (c, d)) * (Y c d + Y d c)

theorem readback_zero_lt {x : TPs S m} (hx : x ∈ currentCarrier S.fullMatrix m 0) (hlt : a < b)
    (r : Option S.ρ) :
    collisionMap (ia a) (ia b) (ia_ne a b (ne_of_lt hlt)) (relF r (pairTable x a b t)) = 0 := by
  have h := hx.2 r ⟨(a, b), hlt⟩ t
  unfold currentReadback projectedDiagonal at h
  rw [Fintype.sum_prod_type] at h
  simp only [relF, map_sum, map_mul, collisionMap, rename_C] at h ⊢
  exact h

include hab in
theorem pairTable_comm (x : TPs S m) (c d : Fin S.n) :
    pairTable x b a t c d = pairTable x a b t d c := by
  simp only [pairTable, pairLabel]
  rw [Function.update_comm (Ne.symm hab)]

include hab in
theorem relF_swap {x : TPs S m} (hx : x ∈ currentCarrier S.fullMatrix m 0) (r : Option S.ρ) :
    relF r (pairTable x b a t) = swapVariables (ia a) (ia b) (relF r (pairTable x a b t)) := by
  simp only [relF, map_sum, map_mul, swapVariables, rename_C]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  rw [pairTable_comm a b hab, pairTable_swap a b hab t hx]
  rfl

include hab in
theorem collisionFactor_dvd_relF {x : TPs S m} (hx : x ∈ currentCarrier S.fullMatrix m 0)
    (r : Option S.ρ) : collisionFactor (K := ℂ) (ia a) (ia b) ∣ relF r (pairTable x a b t) := by
  rcases lt_or_gt_of_ne hab with hlt | hgt
  · exact (collisionFactor_dvd_iff _ _ (ia_ne a b hab) _).2 (readback_zero_lt a b t hx hlt r)
  · have h := (collisionFactor_dvd_iff _ _ (ia_ne b a (Ne.symm hab)) _).2
      (readback_zero_lt b a t hx hgt r)
    rw [relF_swap a b hab t hx] at h
    have h2 := map_dvd (swapVariables (K := ℂ) (ia a) (ia b)) h
    have hcf : swapVariables (K := ℂ) (ia a) (ia b) (collisionFactor (ia b) (ia a)) =
        collisionFactor (ia a) (ia b) := by
      simp [collisionFactor, swapVariables]
    rwa [swap_swap, hcf] at h2

include hab in
theorem relSym_eq {x : TPs S m} (hx : x ∈ currentCarrier S.fullMatrix m 0) (r : Option S.ρ) :
    relSym r (pairTable x a b t) =
      relF r (pairTable x a b t) + swapVariables (ia a) (ia b) (relF r (pairTable x a b t)) := by
  simp only [relSym, relF, mul_add, Finset.sum_add_distrib, map_sum, map_mul, swapVariables,
    rename_C]
  congr 1
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  rw [pairTable_swap a b hab t hx]
  rfl

include hab in
/-- **The relation coordinates of a carrier pair table are divisible by `(z_a - z_b)²`.** -/
theorem relSym_sq_dvd {x : TPs S m} (hx : x ∈ currentCarrier S.fullMatrix m 0)
    (r : Option S.ρ) : zab a b ^ 2 ∣ relSym r (pairTable x a b t) := by
  have hF := collisionFactor_dvd_relF a b hab t hx r
  have hcm : collisionMap (ia a) (ia b) (ia_ne a b hab) (relF r (pairTable x a b t)) = 0 :=
    (collisionFactor_dvd_iff _ _ (ia_ne a b hab) _).1 hF
  refine collisionFactor_sq_dvd_of_swap_invariant (ia a) (ia b) (ia_ne a b hab) _ ?_ ?_
  · rw [relSym_eq a b hab t hx, map_add, swap_swap]
    ring
  · rw [relSym_eq a b hab t hx, map_add, collisionMap_swapVariables, hcm]
    simp

end WSide

end

end VOA.DeligneAudit.DeligneDivisor

section AxiomAudit
#print axioms VOA.DeligneAudit.DeligneDivisor.tensor_eq_sum_pemb
#print axioms VOA.DeligneAudit.DeligneDivisor.good_base
#print axioms VOA.DeligneAudit.DeligneDivisor.pairComparisonG_of_good
#print axioms VOA.DeligneAudit.DeligneDivisor.anti_dvd
#print axioms VOA.DeligneAudit.DeligneDivisor.relSym_sq_dvd
end AxiomAudit
