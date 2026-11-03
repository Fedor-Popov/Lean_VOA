/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.A2SectorGeneric

/-!
# The W side of the pair comparison (step 4 of the `PairComparison` plan)

**Two-slot model** (interface shared with `A2DivisorPairModel`): for a tensor polynomial `x`, two distinct slots
`a ≠ b` and spectator labels `t`, `twoSlot x a b t c d = x (t[a ↦ c][b ↦ d])`, a function
`Fin 8 → Fin 8 → Pm m`, i.e. an element of `g* ⊗ g*` with polynomial coefficients.

**Projectors** on `g* ⊗ g*` adapted to `g ⊗ g = V(2θ) ⊕ I₂ ⊕ Λ²g` (`I₂ = I₂ⁿˢ ⊕ ℂQ`, `fullMatrix`):
* `projL Y = (Y - Yᵀ)/2` (the `Λ²` part);
* `relCoord r Y = Σ_{c,d} Qsym_r(c,d) Y(c,d)` (pairing with the relation `r`, symmetrized);
* `projI Y = Σ_r relCoord r Y · ε_r`, with `ε_r` the symmetric functionals dual to the relations
  (`⟨ε_r, Q_s⟩ = δ_{rs}`) that vanish on `V(2θ)` (computed exactly, `epsSome`, `epsNone`);
* `projV Y = Y - projL Y - projI Y`, which is symmetric and annihilates every relation, i.e. lies in
  the `V(2θ)`-part.

**Divisibility on `W_m`** (`x ∈ currentCarrier fullMatrix m 0`, `a ≠ b`):
* `projL (twoSlot x a b t)` is divisible by `z_a - z_b` (swap symmetry);
* `relCoord r (twoSlot x a b t)` and `projI (twoSlot x a b t)` are divisible by `(z_a - z_b)²`
  (current equations + swap symmetry, `collisionFactor_sq_dvd_of_swap_invariant`).
-/

namespace VOA.DeligneAudit.A2

open MvPolynomial VOA.AffineSl3 VOA.DeligneAudit.SectorLoop VOA.DeligneAudit.SectorFiber
open VOA.QuadraticCurrentFunctionalCarrier VOA.QuadraticJetCoefficientPairing
open VOA.CollisionCommonFactors VOA.DeligneAuxiliaryCollision

noncomputable section

variable {m : ℕ}

/-! ## Two-slot model and projectors -/

/-- **The two-slot part of a tensor polynomial** at slots `a, b` with spectators `t`. -/
def twoSlot (x : TP m) (a b : Fin m) (t : Fin m → Fin 8) : Fin 8 → Fin 8 → Pm m :=
  fun c d => x (Function.update (Function.update t a c) b d)

/-- The symmetrized relation matrices of `I₂ = I₂ⁿˢ ⊕ ℂQ`. -/
def Qsym (r : Option (Fin 8)) (c d : Fin 8) : ℂ := (fullMatrix r (c, d) + fullMatrix r (d, c)) / 2

theorem Qsym_symm (r : Option (Fin 8)) (c d : Fin 8) : Qsym r c d = Qsym r d c := by
  simp only [Qsym, add_comm]

/-- The `Λ²` projector. -/
def projL (Y : Fin 8 → Fin 8 → Pm m) : Fin 8 → Fin 8 → Pm m :=
  fun c d => MvPolynomial.C (1 / 2 : ℂ) * (Y c d - Y d c)

/-- Pairing with the relation `r`. -/
def relCoord (r : Option (Fin 8)) (Y : Fin 8 → Fin 8 → Pm m) : Pm m :=
  ∑ c, ∑ d, MvPolynomial.C (Qsym r c d) * Y c d

def epsSome : Fin 8 → List (Fin 8 × Fin 8 × ℂ) :=
  ![[(0, 7, (1 : ℂ) / 5), (2, 4, (1 : ℂ) / 5), (4, 2, (1 : ℂ) / 5), (7, 0, (1 : ℂ) / 5)],
    [(1, 6, (-1 : ℂ) / 5), (2, 3, (1 : ℂ) / 5), (3, 2, (1 : ℂ) / 5), (6, 1, (-1 : ℂ) / 5)],
    [(0, 1, (1 : ℂ) / 5), (1, 0, (1 : ℂ) / 5), (2, 6, (1 : ℂ) / 5), (2, 7, (-1 : ℂ) / 5),
      (6, 2, (1 : ℂ) / 5), (7, 2, (-1 : ℂ) / 5)],
    [(1, 5, (1 : ℂ) / 5), (3, 7, (1 : ℂ) / 5), (5, 1, (1 : ℂ) / 5), (7, 3, (1 : ℂ) / 5)],
    [(0, 5, (1 : ℂ) / 5), (4, 6, (-1 : ℂ) / 5), (5, 0, (1 : ℂ) / 5), (6, 4, (-1 : ℂ) / 5)],
    [(3, 4, (1 : ℂ) / 5), (4, 3, (1 : ℂ) / 5), (5, 6, (1 : ℂ) / 5), (5, 7, (-1 : ℂ) / 5),
      (6, 5, (1 : ℂ) / 5), (7, 5, (-1 : ℂ) / 5)],
    [(0, 3, (1 : ℂ) / 15), (1, 4, (-2 : ℂ) / 15), (2, 5, (1 : ℂ) / 15), (3, 0, (1 : ℂ) / 15),
      (4, 1, (-2 : ℂ) / 15), (5, 2, (1 : ℂ) / 15), (6, 6, (2 : ℂ) / 15), (6, 7, (2 : ℂ) / 15),
      (7, 6, (2 : ℂ) / 15), (7, 7, (-4 : ℂ) / 15)],
    [(0, 3, (2 : ℂ) / 15), (1, 4, (-1 : ℂ) / 15), (2, 5, (-1 : ℂ) / 15), (3, 0, (2 : ℂ) / 15),
      (4, 1, (-1 : ℂ) / 15), (5, 2, (-1 : ℂ) / 15), (6, 6, (4 : ℂ) / 15),
      (6, 7, (-2 : ℂ) / 15), (7, 6, (-2 : ℂ) / 15), (7, 7, (-2 : ℂ) / 15)]]

def epsNone : List (Fin 8 × Fin 8 × ℂ) :=
  [(0, 3, (1 : ℂ) / 24), (1, 4, (1 : ℂ) / 24), (2, 5, (1 : ℂ) / 24), (3, 0, (1 : ℂ) / 24),
      (4, 1, (1 : ℂ) / 24), (5, 2, (1 : ℂ) / 24), (6, 6, (1 : ℂ) / 12), (6, 7, (-1 : ℂ) / 24),
      (7, 6, (-1 : ℂ) / 24), (7, 7, (1 : ℂ) / 12)]

/-- The symmetric functionals dual to the relations, vanishing on `V(2θ)`. -/
def epsI : Option (Fin 8) → Fin 8 → Fin 8 → ℂ
  | none => fun c d => entryMatrix epsNone (c, d)
  | some a => fun c d => entryMatrix (epsSome a) (c, d)

/-- The `I₂` projector. -/
def projI (Y : Fin 8 → Fin 8 → Pm m) : Fin 8 → Fin 8 → Pm m :=
  fun c d => ∑ r : Option (Fin 8), MvPolynomial.C (epsI r c d) * relCoord r Y

/-- The `V(2θ)` projector. -/
def projV (Y : Fin 8 → Fin 8 → Pm m) : Fin 8 → Fin 8 → Pm m :=
  fun c d => Y c d - projL Y c d - projI Y c d

theorem decomp (Y : Fin 8 → Fin 8 → Pm m) (c d : Fin 8) :
    Y c d = projV Y c d + projL Y c d + projI Y c d := by
  simp only [projV]; ring

/-! ## Exact duality data -/

set_option maxHeartbeats 4000000 in -- 81 explicit 64-term sums
/-- **Duality**: `⟨Qsym_r, ε_s⟩ = δ_{rs}`. -/
theorem pair_Qsym_eps (r s : Option (Fin 8)) :
    ∑ c, ∑ d, Qsym r c d * epsI s c d = if r = s then 1 else 0 := by
  cases r with
  | none =>
      cases s with
      | none =>
          simp [Fin.sum_univ_eight, Qsym, epsI, fullMatrix, casimirMatrix, entryMatrix, epsNone]
          norm_num
      | some b =>
          fin_cases b <;>
          simp [Fin.sum_univ_eight, Qsym, epsI, fullMatrix, casimirMatrix, entryMatrix, epsSome]
          <;> norm_num
  | some a =>
      cases s with
      | none =>
          fin_cases a <;>
          simp [Fin.sum_univ_eight, Qsym, epsI, fullMatrix, relationMatrix, relationEntries,
            entryMatrix, epsNone] <;> norm_num
      | some b =>
          fin_cases a <;> fin_cases b <;>
          simp [Fin.sum_univ_eight, Qsym, epsI, fullMatrix, relationMatrix, relationEntries,
            entryMatrix, epsSome] <;> norm_num

set_option maxHeartbeats 4000000 in -- 576 table entries
theorem epsI_symm (r : Option (Fin 8)) (c d : Fin 8) : epsI r c d = epsI r d c := by
  cases r with
  | none => fin_cases c <;> fin_cases d <;> simp [epsI, entryMatrix, epsNone]
  | some a =>
      fin_cases a <;> fin_cases c <;> fin_cases d <;> simp [epsI, entryMatrix, epsSome]

/-! ## Projector identities -/

theorem relCoord_projL (r : Option (Fin 8)) (Y : Fin 8 → Fin 8 → Pm m) :
    relCoord r (projL Y) = 0 := by
  have h : relCoord r (projL Y) = -relCoord r (projL Y) := by
    unfold relCoord
    conv_rhs => rw [Finset.sum_comm]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    simp only [projL, Qsym_symm r c d]
    ring
  have h2 : (2 : Pm m) * relCoord r (projL Y) = 0 := by
    rw [two_mul]; nth_rewrite 2 [h]; exact add_neg_cancel _
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd h3 two_ne_zero
  · exact h3

theorem triple_sum_swap {R ι κ : Type*} [CommRing R] [Fintype ι] [Fintype κ]
    (q : ι → ι → R) (e : κ → ι → ι → R) (u : κ → R) :
    (∑ c, ∑ d, q c d * ∑ s, e s c d * u s) = ∑ s, (∑ c, ∑ d, q c d * e s c d) * u s := by
  simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
  rw [Finset.sum_congr rfl fun c _ => Finset.sum_comm]
  exact Finset.sum_comm

theorem relCoord_projI (r : Option (Fin 8)) (Y : Fin 8 → Fin 8 → Pm m) :
    relCoord r (projI Y) = relCoord r Y := by
  have h : relCoord r (projI Y) = ∑ s : Option (Fin 8),
      (∑ c, ∑ d, MvPolynomial.C (Qsym r c d) * MvPolynomial.C (epsI s c d)) * relCoord s Y :=
    triple_sum_swap (fun c d => MvPolynomial.C (Qsym r c d))
      (fun s c d => MvPolynomial.C (epsI s c d)) (fun s => relCoord s Y)
  rw [h]
  have h2 : ∀ s : Option (Fin 8),
      (∑ c, ∑ d, (MvPolynomial.C (Qsym r c d) : Pm m) * MvPolynomial.C (epsI s c d)) =
        MvPolynomial.C (∑ c, ∑ d, Qsym r c d * epsI s c d) := by
    intro s; simp only [map_sum, map_mul]
  simp only [h2, pair_Qsym_eps, apply_ite MvPolynomial.C, map_one, map_zero, ite_mul, one_mul,
    zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- **The `V(2θ)` part annihilates every relation.** -/
theorem relCoord_projV (r : Option (Fin 8)) (Y : Fin 8 → Fin 8 → Pm m) :
    relCoord r (projV Y) = 0 := by
  have hlin : relCoord r (projV Y) = relCoord r Y - relCoord r (projL Y) - relCoord r (projI Y) := by
    simp only [relCoord, projV, mul_sub, Finset.sum_sub_distrib]
  rw [hlin, relCoord_projL, relCoord_projI]
  ring

/-- **The `V(2θ)` part is symmetric.** -/
theorem projV_symm (Y : Fin 8 → Fin 8 → Pm m) (c d : Fin 8) : projV Y c d = projV Y d c := by
  simp only [projV, projL, projI, epsI_symm _ c d]
  have h2 : (MvPolynomial.C (1 / 2 : ℂ) : Pm m) * 2 = 1 := by
    rw [show (2 : Pm m) = MvPolynomial.C 2 from (map_ofNat _ 2).symm, ← map_mul]; norm_num
  linear_combination (Y d c - Y c d) * h2

theorem projL_antisymm (Y : Fin 8 → Fin 8 → Pm m) (c d : Fin 8) : projL Y c d = -projL Y d c := by
  simp only [projL]; ring

/-- A symmetric two-slot tensor annihilated by all relations is its own `V(2θ)` part. -/
theorem projV_eq_self {Y : Fin 8 → Fin 8 → Pm m} (hs : ∀ c d, Y c d = Y d c)
    (hr : ∀ r, relCoord r Y = 0) (c d : Fin 8) : projV Y c d = Y c d := by
  simp only [projV, projL, projI, hr, mul_zero, Finset.sum_const_zero, sub_zero, hs c d, sub_self]

/-- The `I₂` part is a combination of the dual functionals `ε_r`. -/
theorem projI_apply (Y : Fin 8 → Fin 8 → Pm m) (c d : Fin 8) :
    projI Y c d = ∑ r : Option (Fin 8), MvPolynomial.C (epsI r c d) * relCoord r Y := rfl

/-! ## The W side: divisibility of the two-slot components -/

section WSide

variable (a b : Fin m) (hab : a ≠ b) (t : Fin m → Fin 8)

/-- The root variables of the two slots. -/
abbrev ia : Fin (m + 0) := Fin.castAdd 0 a

theorem ia_ne (hab : a ≠ b) : ia b ≠ ia a := (Fin.castAdd_injective m 0).ne (Ne.symm hab)

include hab in
theorem update_swap_comp (c d : Fin 8) :
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
/-- **Swap symmetry of the two-slot part.** -/
theorem twoSlot_swap {x : TP m} (hx : x ∈ currentCarrier fullMatrix m 0) (c d : Fin 8) :
    twoSlot x a b t d c = swapVariables (ia a) (ia b) (twoSlot x a b t c d) := by
  have he : ExtendsCurrentPermutation (Equiv.swap (ia a) (ia b)) (Equiv.swap a b) := fun k =>
    (Fin.castAdd_injective m 0).swap_apply _ _ _
  have h := hx.1 _ _ he (Function.update (Function.update t a c) b d)
  rw [update_swap_comp a b hab] at h
  exact h.symm

include hab in
/-- **The `Λ²` part of a carrier vector is divisible by `z_a - z_b`.** -/
theorem projL_dvd {x : TP m} (hx : x ∈ currentCarrier fullMatrix m 0) (c d : Fin 8) :
    (zr (K := ℂ) a - zr b) ∣ projL (twoSlot x a b t) c d := by
  simp only [projL]
  rw [twoSlot_swap a b hab t hx c d]
  exact dvd_mul_of_dvd_right
    (collisionFactor_dvd_sub_swapVariables (ia a) (ia b) (ia_ne a b hab) _) _

/-- The unsymmetrized pairing with a relation. -/
def relF (r : Option (Fin 8)) (Y : Fin 8 → Fin 8 → Pm m) : Pm m :=
  ∑ c, ∑ d, MvPolynomial.C (fullMatrix r (c, d)) * Y c d

theorem readback_zero_lt {x : TP m} (hx : x ∈ currentCarrier fullMatrix m 0) (hlt : a < b)
    (r : Option (Fin 8)) :
    collisionMap (ia a) (ia b) (ia_ne a b (ne_of_lt hlt)) (relF r (twoSlot x a b t)) = 0 := by
  have h := hx.2 r ⟨(a, b), hlt⟩ t
  unfold currentReadback projectedDiagonal at h
  rw [Fintype.sum_prod_type] at h
  simp only [relF, map_sum, map_mul, collisionMap, rename_C] at h ⊢
  exact h

include hab in
theorem twoSlot_comm (x : TP m) (c d : Fin 8) : twoSlot x b a t c d = twoSlot x a b t d c := by
  simp only [twoSlot]
  rw [Function.update_comm (Ne.symm hab)]

include hab in
theorem relF_swap {x : TP m} (hx : x ∈ currentCarrier fullMatrix m 0) (r : Option (Fin 8)) :
    relF r (twoSlot x b a t) = swapVariables (ia a) (ia b) (relF r (twoSlot x a b t)) := by
  simp only [relF, map_sum, map_mul, swapVariables, rename_C]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  rw [twoSlot_comm a b hab, twoSlot_swap a b hab t hx]
  rfl

include hab in
theorem collisionFactor_dvd_relF {x : TP m} (hx : x ∈ currentCarrier fullMatrix m 0)
    (r : Option (Fin 8)) : collisionFactor (K := ℂ) (ia a) (ia b) ∣ relF r (twoSlot x a b t) := by
  rcases lt_or_gt_of_ne hab with hlt | hgt
  · exact (collisionFactor_dvd_iff _ _ (ia_ne a b hab) _).2 (readback_zero_lt a b t hx hlt r)
  · have h := (collisionFactor_dvd_iff _ _ (ia_ne b a (Ne.symm hab)) _).2
      (readback_zero_lt b a t hx hgt r)
    rw [relF_swap a b hab t hx] at h
    have h2 := map_dvd (swapVariables (K := ℂ) (ia a) (ia b)) h
    have hsw : swapVariables (K := ℂ) (ia a) (ia b) (swapVariables (ia a) (ia b) (relF r (twoSlot x a b t)))
        = relF r (twoSlot x a b t) := by
      have hid : (⇑(Equiv.swap (ia a) (ia b)) ∘ ⇑(Equiv.swap (ia a) (ia b))) = id :=
        funext fun k => Equiv.swap_apply_self _ _ k
      simp only [swapVariables, rename_rename, hid, rename_id_apply]
    have hcf : swapVariables (K := ℂ) (ia a) (ia b) (collisionFactor (ia b) (ia a)) =
        collisionFactor (ia a) (ia b) := by
      simp [collisionFactor, swapVariables]
    rwa [hsw, hcf] at h2

theorem relCoord_eq (r : Option (Fin 8)) (Y : Fin 8 → Fin 8 → Pm m) :
    relCoord r Y = MvPolynomial.C (1 / 2 : ℂ) *
      (relF r Y + ∑ c, ∑ d, MvPolynomial.C (fullMatrix r (c, d)) * Y d c) := by
  have e2 : (∑ c, ∑ d, MvPolynomial.C (fullMatrix r (d, c)) * Y c d) =
      ∑ c, ∑ d, (MvPolynomial.C (fullMatrix r (c, d)) : Pm m) * Y d c := Finset.sum_comm
  rw [← e2]
  simp only [relCoord, relF, Qsym, mul_add, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  rw [show ((fullMatrix r (c, d) + fullMatrix r (d, c)) / 2 : ℂ) =
    (1 / 2) * (fullMatrix r (c, d) + fullMatrix r (d, c)) by ring, map_mul, map_add]
  ring

theorem swap_swap (P : Pm m) :
    swapVariables (K := ℂ) (ia a) (ia b) (swapVariables (ia a) (ia b) P) = P := by
  have hid : (⇑(Equiv.swap (ia a) (ia b)) ∘ ⇑(Equiv.swap (ia a) (ia b))) = id :=
    funext fun k => Equiv.swap_apply_self _ _ k
  simp only [swapVariables, rename_rename, hid, rename_id_apply]

include hab in
theorem relCoord_twoSlot_eq {x : TP m} (hx : x ∈ currentCarrier fullMatrix m 0)
    (r : Option (Fin 8)) :
    relCoord r (twoSlot x a b t) = MvPolynomial.C (1 / 2 : ℂ) *
      (relF r (twoSlot x a b t) + swapVariables (ia a) (ia b) (relF r (twoSlot x a b t))) := by
  rw [relCoord_eq]
  congr 2
  simp only [relF, map_sum, map_mul, swapVariables, rename_C]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  rw [twoSlot_swap a b hab t hx]
  rfl

include hab in
/-- **The `I₂` coordinates of a carrier vector are divisible by `(z_a - z_b)²`.** -/
theorem relCoord_sq_dvd {x : TP m} (hx : x ∈ currentCarrier fullMatrix m 0)
    (r : Option (Fin 8)) : (zr (K := ℂ) a - zr b) ^ 2 ∣ relCoord r (twoSlot x a b t) := by
  have hF := collisionFactor_dvd_relF a b hab t hx r
  have hcm : collisionMap (ia a) (ia b) (ia_ne a b hab) (relF r (twoSlot x a b t)) = 0 :=
    (collisionFactor_dvd_iff _ _ (ia_ne a b hab) _).1 hF
  refine collisionFactor_sq_dvd_of_swap_invariant (ia a) (ia b) (ia_ne a b hab) _ ?_ ?_
  · rw [relCoord_twoSlot_eq a b hab t hx, map_mul, map_add, swap_swap]
    simp only [swapVariables, rename_C]
    ring
  · rw [relCoord_twoSlot_eq a b hab t hx, map_mul, map_add, collisionMap_swapVariables, hcm]
    simp

include hab in
/-- **The `I₂` part of a carrier vector is divisible by `(z_a - z_b)²`.** -/
theorem projI_sq_dvd {x : TP m} (hx : x ∈ currentCarrier fullMatrix m 0) (c d : Fin 8) :
    (zr (K := ℂ) a - zr b) ^ 2 ∣ projI (twoSlot x a b t) c d :=
  Finset.dvd_sum fun r _ => dvd_mul_of_dvd_right (relCoord_sq_dvd a b hab t hx r) _

end WSide

end

end VOA.DeligneAudit.A2

section AxiomAudit
#print axioms VOA.DeligneAudit.A2.pair_Qsym_eps
#print axioms VOA.DeligneAudit.A2.relCoord_projV
#print axioms VOA.DeligneAudit.A2.projV_symm
#print axioms VOA.DeligneAudit.A2.projL_dvd
#print axioms VOA.DeligneAudit.A2.relCoord_sq_dvd
#print axioms VOA.DeligneAudit.A2.projI_sq_dvd
end AxiomAudit
