/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneSectorModule
import VOA.DeligneAudit.A2SectorGeneric

/-!
# The generic comparison `Δ^L W_m ⊂ M_m` (type-generic)

Interpolation over `P_m` gives single-slot operators `D_i x^{(i)}` on `P_m M_m`; coadjoint
cyclicity in depth `L` (`S.cyclic`) moves every slot label, costing `D_i^L`; Reynolds descends to
`M_m`.  For A₂, `L = 3`.
-/

namespace VOA.DeligneAudit.DeligneSector

open MvPolynomial VOA.DeligneAudit.SectorLoop VOA.DeligneAudit.SectorFiber
open VOA.DeligneAudit.SectorFiberModule VOA.QuadraticCurrentFunctionalCarrier
open VOA.DeligneAudit.A2 (Pm Dslot Lpoly eval_Lpoly discS discS_coe symP card_perm_ne_zero
  discS_ne_zero)

noncomputable section

variable {S : DeligneSectorData} {m : ℕ}

theorem psmul_apply (p : Pm m) (v : TPs S m) (t : Fin m → Fin S.n) : (p • v) t = p * v t := rfl

/-- `x` acting in slot `i` only (coadjoint). -/
def slotOp (x : Fin S.n) (i : Fin m) : TPs S m →ₗ[ℂ] TPs S m where
  toFun p t := -∑ c, MvPolynomial.C (S.f x (t i) c) * p (Function.update t i c)
  map_add' p q := by funext t; simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, neg_add]
  map_smul' a p := by
    funext t
    simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_C_mul, Finset.mul_sum, mul_neg]
    congr 1
    refine Finset.sum_congr rfl fun c _ => ?_
    ring

theorem loopOp_eq_sum_slot (x : Fin S.n) (r : ℕ) (v : TPs S m) :
    loopOp S.f m x r v = ∑ i, (zr (K := ℂ) i ^ r : Pm m) • slotOp x i v := by
  funext t
  simp only [loopOp, slotOp, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply, psmul_apply,
    mul_neg, Finset.sum_neg_distrib]

theorem slotOp_psmul (x : Fin S.n) (i : Fin m) (p : Pm m) (v : TPs S m) :
    slotOp x i (p • v) = p • slotOp x i v := by
  funext t
  simp only [slotOp, LinearMap.coe_mk, AddHom.coe_mk, psmul_apply, Finset.mul_sum, mul_neg]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  ring

theorem loopOp_psmul (x : Fin S.n) (r : ℕ) (p : Pm m) (v : TPs S m) :
    loopOp S.f m x r (p • v) = p • loopOp S.f m x r v := by
  rw [loopOp_eq_sum_slot, loopOp_eq_sum_slot, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [slotOp_psmul, smul_smul, smul_smul, mul_comm]

theorem loopOp_mem_Mspace (x : Fin S.n) (r : ℕ) {v : TPs S m}
    (hv : v ∈ Mspace S.f m S.c₀) :
    loopOp S.f m x r v ∈ Mspace S.f m S.c₀ := by
  induction hv using Submodule.span_induction with
  | mem w hw =>
      obtain ⟨l, rfl⟩ := hw
      exact Submodule.subset_span ⟨(x, r) :: l, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha

variable (S) in
/-- `P_m · M_m`. -/
def MP (m : ℕ) : Submodule (Pm m) (TPs S m) :=
  Submodule.span (Pm m) (Mspace S.f m S.c₀ : Set (TPs S m))

theorem loopOp_mem_MP (x : Fin S.n) (r : ℕ) {v : TPs S m} (hv : v ∈ MP S m) :
    loopOp S.f m x r v ∈ MP S m := by
  induction hv using Submodule.span_induction with
  | mem w hw => exact Submodule.subset_span (loopOp_mem_Mspace x r hw)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
  | smul p a _ ha => rw [loopOp_psmul]; exact Submodule.smul_mem _ p ha

/-- **Interpolation**: a `P_m`-combination of loop operators acts in one slot only. -/
theorem interp (x : Fin S.n) (i : Fin m) (v : TPs S m) :
    ∑ r ∈ Finset.range ((Lpoly i).natDegree + 1),
        ((Lpoly i).coeff r) • loopOp S.f m x r v = Dslot i • slotOp x i v := by
  simp only [loopOp_eq_sum_slot, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul]
  have h : ∀ k : Fin m, (∑ r ∈ Finset.range ((Lpoly i).natDegree + 1),
      (Lpoly i).coeff r * zr (K := ℂ) k ^ r) = if k = i then Dslot i else 0 := by
    intro k
    rw [← eval_Lpoly, Polynomial.eval_eq_sum_range]
  simp only [h, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem Dslot_slotOp_mem_MP (x : Fin S.n) (i : Fin m) {v : TPs S m} (hv : v ∈ MP S m) :
    Dslot i • slotOp x i v ∈ MP S m := by
  rw [← interp]
  exact Submodule.sum_mem _ fun r _ => Submodule.smul_mem _ _ (loopOp_mem_MP x r hv)

/-- The basis tensor `δ_t`. -/
def deltaT (t : Fin m → Fin S.n) : TPs S m := fun t' => if t' = t then 1 else 0

theorem slotOp_deltaT (x : Fin S.n) (i : Fin m) (t : Fin m → Fin S.n) :
    slotOp x i (deltaT t) =
      ∑ y, (MvPolynomial.C (-S.f x y (t i)) : Pm m) • deltaT (Function.update t i y) := by
  funext t'
  simp only [slotOp, LinearMap.coe_mk, AddHom.coe_mk, deltaT, Finset.sum_apply, psmul_apply,
    mul_ite, mul_one, mul_zero]
  by_cases h : ∀ j, j ≠ i → t' j = t j
  · have h1 : ∀ c, (Function.update t' i c = t ↔ c = t i) := by
      intro c
      constructor
      · intro hc; rw [← hc]; simp
      · rintro rfl; funext j; by_cases hj : j = i
        · subst hj; simp
        · rw [Function.update_of_ne hj, h j hj]
    have h2 : ∀ y, (t' = Function.update t i y ↔ y = t' i) := by
      intro y
      constructor
      · rintro rfl; simp
      · rintro rfl; funext j; by_cases hj : j = i
        · subst hj; simp
        · rw [Function.update_of_ne hj, h j hj]
    simp only [h1, h2, Finset.sum_ite_eq', Finset.mem_univ, if_true, map_neg]
  · have h1 : ∀ c, ¬ (Function.update t' i c = t) := by
      intro c hc; apply h; intro j hj; rw [← hc, Function.update_of_ne hj]
    have h2 : ∀ y, ¬ (t' = Function.update t i y) := by
      intro y hy; apply h; intro j hj; rw [hy, Function.update_of_ne hj]
    simp [h1, h2]

theorem deltaT_update_update (t : Fin m → Fin S.n) (i : Fin m) (a b : Fin S.n) :
    deltaT (m := m) (Function.update (Function.update t i a) i b) =
      deltaT (Function.update t i b) := by
  rw [Function.update_idem]

/-- One slot-step of the recipe, in closed form. -/
theorem slotOp_e (x : Fin S.n) (i : Fin m) (t : Fin m → Fin S.n) (a : Fin S.n) :
    slotOp x i (deltaT (Function.update t i a)) =
      ∑ y, (MvPolynomial.C (-S.f x y a) : Pm m) • deltaT (Function.update t i y) := by
  rw [slotOp_deltaT]
  simp only [Function.update_self, deltaT_update_update]

theorem step_MP (x : Fin S.n) (i : Fin m) {k : ℕ} {v : TPs S m} (hv : Dslot i ^ k • v ∈ MP S m) :
    Dslot i ^ (k + 1) • slotOp x i v ∈ MP S m := by
  rw [pow_succ', mul_smul, ← slotOp_psmul]
  exact Dslot_slotOp_mem_MP x i hv

theorem mono_MP (i : Fin m) {k : ℕ} {v : TPs S m} (hv : Dslot i ^ k • v ∈ MP S m) :
    Dslot i ^ (k + 1) • v ∈ MP S m := by
  rw [pow_succ', mul_smul]
  exact Submodule.smul_mem _ _ hv

theorem mem_of_nsmul_MP (n : ℕ) (hn : n ≠ 0) {v : TPs S m} (hv : (n : Pm m) • v ∈ MP S m) :
    v ∈ MP S m := by
  have h := Submodule.smul_mem (MP S m) (MvPolynomial.C ((n : ℂ)⁻¹)) hv
  rwa [smul_smul, show (MvPolynomial.C ((n : ℂ)⁻¹) : Pm m) * (n : Pm m) = 1 by
    rw [← map_natCast MvPolynomial.C n, ← map_mul, inv_mul_cancel₀ (by exact_mod_cast hn),
      map_one], one_smul] at h


/-! ## One slot, from coadjoint cyclicity -/

/-- The one-slot embedding `g* → TP`, `v ↦ Σ_c v(c) δ_{t[i↦c]}`. -/
def emb (i : Fin m) (t : Fin m → Fin S.n) (v : Fin S.n → ℂ) : TPs S m :=
  ∑ c, (MvPolynomial.C (v c) : Pm m) • deltaT (Function.update t i c)

theorem emb_add (i : Fin m) (t : Fin m → Fin S.n) (v w : Fin S.n → ℂ) :
    emb i t (v + w) = emb i t v + emb i t w := by
  simp only [emb, Pi.add_apply, map_add, add_smul, Finset.sum_add_distrib]

theorem emb_smul (i : Fin m) (t : Fin m → Fin S.n) (a : ℂ) (v : Fin S.n → ℂ) :
    emb i t (a • v) = (MvPolynomial.C a : Pm m) • emb i t v := by
  simp only [emb, Pi.smul_apply, smul_eq_mul, map_mul, Finset.smul_sum, smul_smul]

theorem emb_single (i : Fin m) (t : Fin m → Fin S.n) (c : Fin S.n) :
    emb i t (Pi.single c 1) = deltaT (Function.update t i c) := by
  classical
  rw [emb, Finset.sum_eq_single c]
  · simp
  · intro b _ hb; simp [Pi.single_apply, hb]
  · simp

theorem slotOp_emb (x : Fin S.n) (i : Fin m) (t : Fin m → Fin S.n) (v : Fin S.n → ℂ) :
    slotOp x i (emb i t v) = emb i t (DeligneSector.slotA S.f x v) := by
  simp only [emb, map_sum, slotOp_psmul, slotOp_e, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [← Finset.sum_smul]
  congr 1
  simp only [slotA, map_neg, map_sum, map_mul, mul_neg, Finset.sum_neg_distrib]
  congr 1
  exact Finset.sum_congr rfl fun d _ => mul_comm _ _

theorem emb_wordA_mem (i : Fin m) (t : Fin m → Fin S.n) (Q : Pm m)
    (hQ : Q • emb i t (Pi.single S.c₀ 1) ∈ MP S m) :
    ∀ l : List (Fin S.n), Dslot i ^ l.length • Q • emb i t (wordA S.f l (Pi.single S.c₀ 1)) ∈ MP S m
  | [] => by simpa using hQ
  | (x :: l) => by
      have h := step_MP x i (emb_wordA_mem i t Q hQ l)
      simp only [List.length_cons]
      rw [show wordA S.f (x :: l) (Pi.single S.c₀ 1) = slotA S.f x (wordA S.f l (Pi.single S.c₀ 1))
        from rfl, ← slotOp_emb, ← slotOp_psmul]
      exact h

/-- **One slot**: every label `c` is reached with the factor `D_i^L`. -/
theorem slot_all (i : Fin m) (t : Fin m → Fin S.n) (Q : Pm m)
    (hQ : Q • deltaT (Function.update t i S.c₀) ∈ MP S m) (c : Fin S.n) :
    (Dslot i ^ S.depth * Q) • deltaT (Function.update t i c) ∈ MP S m := by
  rw [← emb_single] at hQ ⊢
  let G : Submodule ℂ (Fin S.n → ℂ) :=
    { carrier := {v | (Dslot i ^ S.depth * Q) • emb i t v ∈ MP S m}
      zero_mem' := by
        simp only [Set.mem_setOf_eq]
        have : emb i t (0 : Fin S.n → ℂ) = 0 := by simp [emb]
        rw [this, smul_zero]; exact Submodule.zero_mem _
      add_mem' := fun {v w} hv hw => by
        simp only [Set.mem_setOf_eq] at hv hw ⊢
        rw [emb_add, smul_add]; exact Submodule.add_mem _ hv hw
      smul_mem' := fun a v hv => by
        simp only [Set.mem_setOf_eq] at hv ⊢
        rw [emb_smul, smul_comm]; exact Submodule.smul_mem _ _ hv }
  have hle : slotWords S.f S.c₀ S.depth ≤ G := by
    rw [slotWords, Submodule.span_le]
    rintro _ ⟨l, hl, rfl⟩
    show (Dslot i ^ S.depth * Q) • emb i t (wordA S.f l (Pi.single S.c₀ 1)) ∈ MP S m
    have h := emb_wordA_mem i t Q hQ l
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hl
    have hpow : ∀ j, Dslot i ^ (l.length + j) • Q • emb i t (wordA S.f l (Pi.single S.c₀ 1))
        ∈ MP S m := by
      intro j
      induction j with
      | zero => simpa using h
      | succ j ih => rw [← add_assoc]; exact mono_MP i ih
    have := hpow k
    rwa [← hk, smul_smul] at this
  exact hle (S.cyclic c)

/-! ## All slots -/
theorem all_slots (J : Finset (Fin m)) :
    ∀ t : Fin m → Fin S.n, (∀ j, j ∉ J → t j = S.c₀) →
      (∏ j ∈ J, Dslot j ^ S.depth) • deltaT t ∈ MP S m := by
  classical
  induction J using Finset.induction_on with
  | empty =>
      intro t ht
      have : t = fun _ => S.c₀ := funext fun j => ht j (Finset.notMem_empty j)
      subst this
      rw [Finset.prod_empty, one_smul]
      exact Submodule.subset_span (Submodule.subset_span ⟨[], rfl⟩)
  | insert i J hi ih =>
      intro t ht
      set t' := Function.update t i S.c₀ with ht'
      have hJ : ∀ j, j ∉ J → t' j = S.c₀ := by
        intro j hj
        by_cases hji : j = i
        · subst hji; simp [t']
        · rw [ht', Function.update_of_ne hji]
          exact ht j (by simp [hji, hj])
      have h1 := ih t' hJ
      have he5 : deltaT (Function.update t' i S.c₀) = deltaT t' := by
        simp only [t', Function.update_idem]
      rw [← he5] at h1
      have h2 := slot_all i t' _ h1 (t i)
      have het : deltaT (Function.update t' i (t i)) = deltaT t := by
        simp only [t', Function.update_idem, Function.update_eq_self]
      rw [het] at h2
      rwa [Finset.prod_insert hi]

theorem tensor_eq_sum (x : TPs S m) : x = ∑ t, x t • deltaT t := by
  funext t'
  simp [Finset.sum_apply, deltaT]

/-- **`Δ³ · v ∈ P_m M_m` for every tensor polynomial `v`.** -/
theorem disc_pow_mem_MP (x : TPs S m) : ((discS m : Pm m) ^ S.depth) • x ∈ MP S m := by
  rw [tensor_eq_sum x, Finset.smul_sum]
  refine Submodule.sum_mem _ fun t _ => ?_
  rw [smul_comm]
  refine Submodule.smul_mem _ _ ?_
  rw [discS_coe, ← Finset.prod_pow]
  exact all_slots Finset.univ t (fun j hj => absurd (Finset.mem_univ j) hj)

/-! ## The Reynolds operator -/

/-- Simultaneous permutation of slots and roots. -/
def act (g : Equiv.Perm (Fin m)) (v : TPs S m) : TPs S m := fun t => rename (⇑g) (v (t ∘ g))

theorem act_of_symmetric {v : TPs S m} (hv : Symmetric v) (g : Equiv.Perm (Fin m)) :
    act g v = v := by
  funext t
  have h := hv (g : Equiv.Perm (Fin (m + 0))) g (fun i => rfl) (t ∘ g)
  simp only [act]
  rw [h, Function.comp_assoc, Equiv.self_comp_symm, Function.comp_id]

theorem act_psmul (g : Equiv.Perm (Fin m)) (p : Pm m) (v : TPs S m) :
    act g (p • v) = rename (⇑g) p • act g v := by
  funext t
  simp only [act, psmul_apply, map_mul]

theorem act_add (g : Equiv.Perm (Fin m)) (v w : TPs S m) : act g (v + w) = act g v + act g w := by
  funext t; simp [act]

theorem act_sum (g : Equiv.Perm (Fin m)) {ι : Type*} (T : Finset ι) (v : ι → TPs S m) :
    act g (∑ k ∈ T, v k) = ∑ k ∈ T, act g (v k) := by
  funext t; simp [act, Finset.sum_apply, map_sum]

/-- **Reynolds**: a symmetric tensor in `P_m M_m` lies in `M_m`. -/
theorem mem_Mspace_of_symmetric {v : TPs S m} (hv : v ∈ MP S m) (hs : Symmetric v) :
    v ∈ Mspace S.f m S.c₀ := by
  classical
  obtain ⟨n, f, y, rfl⟩ := Submodule.mem_span_set'.mp hv
  -- average over the symmetric group
  have hsum : (∑ i, f i • (y i : TPs S m)) =
      ∑ i, (symP (f i) : SymAlg (K := ℂ) m) • (y i : TPs S m) := by
    have hy : ∀ i, Symmetric (y i : TPs S m) := fun i =>
      (Mspace_le S.f S.stable S.c₀ S.diag (y i).2).1
    have key : ∀ g : Equiv.Perm (Fin m), act g (∑ i, f i • (y i : TPs S m)) = ∑ i, f i • (y i : TPs S m) :=
      fun g => act_of_symmetric hs g
    have havg : (∑ i, f i • (y i : TPs S m)) =
        (MvPolynomial.C ((Fintype.card (Equiv.Perm (Fin m)) : ℂ)⁻¹) : Pm m) •
          ∑ g : Equiv.Perm (Fin m), act g (∑ i, f i • (y i : TPs S m)) := by
      simp only [key, Finset.sum_const, Finset.card_univ]
      rw [← Nat.cast_smul_eq_nsmul (Pm m), smul_smul, ← map_natCast MvPolynomial.C, ← map_mul,
        inv_mul_cancel₀ card_perm_ne_zero, map_one, one_smul]
    rw [havg]
    simp only [act_sum, act_psmul, act_of_symmetric (hy _)]
    rw [Finset.sum_comm, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    funext t
    simp only [psmul_apply, smul_apply_sym, symP, Finset.sum_apply, Finset.sum_mul, mul_assoc]
  rw [hsum]
  exact Submodule.sum_mem _ fun i _ => smul_mem_Mspace S m _ (y i).2

/-! ## The generic comparison -/

theorem disc_symmetric_smul {x : TPs S m} (hx : Symmetric x) :
    Symmetric (((discS m : Pm m) ^ S.depth) • x) := by
  intro e g he t
  rw [psmul_apply, psmul_apply, map_mul, map_pow, hx e g he t]
  congr 2
  exact (discS m).2 e

variable (S) in
/-- **Generic comparison (type-generic), proved**: `Δ^L W_m ⊂ M_m`, `L = S.depth`. -/
theorem genericComparisonG (m : ℕ) {x : TPs S m} (hx : x ∈ currentCarrier S.fullMatrix m 0) :
    (discS m : SymAlg (K := ℂ) m) ^ S.depth • x ∈ Mspace S.f m S.c₀ := by
  have h1 := mem_Mspace_of_symmetric (disc_pow_mem_MP x) (disc_symmetric_smul hx.1)
  convert h1 using 1

end

end VOA.DeligneAudit.DeligneSector
