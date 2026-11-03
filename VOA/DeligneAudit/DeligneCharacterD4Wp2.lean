/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneCharacterD4Wp

/-!
# The diagonal of the two-variable identity (layer 2)

Applying `∂_b` and then `b = a` to `two_var` gives the one-variable cubic identity

  `D(Ψ²)·2G - Ψ²·D(2G) = -κ · a · Ψ(a²) · J`,   `J = (DΨ)(1)`,

using `Ψ(1) = 0` (`ev_Psi`).
-/

namespace VOA.DeligneAudit.DeligneCharacter.D4Wp

open PowerSeries VOA.QSeries VOA.QSeries.JTP

open scoped BigOperators

noncomputable section

/-- Ring maps `ℚ[a^{±1}] → ℚ[a^{±1}]` from `g : ℤ →+ ℤ`. -/
def embL (g : ℤ →+ ℤ) : L →+* L := AddMonoidAlgebra.mapDomainRingHom ℚ g

/-- The diagonal `a, b ↦ a`. -/
def dg : ℤ × ℤ →+ ℤ := AddMonoidHom.fst ℤ ℤ + AddMonoidHom.snd ℤ ℤ

/-- `ℚ[a^{±1},b^{±1}] → ℚ[a^{±1}]`, `b ↦ a`. -/
def diag : L2 →+* L := AddMonoidAlgebra.mapDomainRingHom ℚ dg

theorem diag_emb (f : ℤ →+ ℤ × ℤ) (x : L) : diag (emb f x) = embL (dg.comp f) x := by
  rw [diag, emb, embL, AddMonoidAlgebra.mapDomainRingHom_apply, AddMonoidAlgebra.mapDomainRingHom_apply,
    AddMonoidAlgebra.mapDomainRingHom_apply]
  exact (Finsupp.mapDomain_comp).symm

theorem map_diag_map_emb (f : ℤ →+ ℤ × ℤ) (F : PowerSeries L) :
    PowerSeries.map diag (PowerSeries.map (emb f) F) = PowerSeries.map (embL (dg.comp f)) F := by
  ext n : 1; simp [diag_emb]

theorem embL_id_eq (g : ℤ →+ ℤ) (hg : ∀ j, g j = j) (x : L) : embL g x = x := by
  have : g = AddMonoidHom.id ℤ := AddMonoidHom.ext hg
  subst this
  rw [embL, AddMonoidAlgebra.mapDomainRingHom_apply]
  exact Finsupp.mapDomain_id

theorem map_embL_id (g : ℤ →+ ℤ) (hg : ∀ j, g j = j) (F : PowerSeries L) :
    PowerSeries.map (embL g) F = F := by
  ext n : 1; simp [embL_id_eq g hg]

/-! ## Derivations through ring maps -/

theorem wd_emb (w : ℤ × ℤ →+ ℤ) (f : ℤ →+ ℤ × ℤ) (x : L) :
    wd w (emb f x) = emb f (wd (w.comp f) x) := by
  induction x using AddMonoidAlgebra.induction_linear with
  | zero => rw [map_zero, wd_zero, wd_zero, map_zero]
  | add x y hx hy => rw [map_add, wd_add, hx, hy, wd_add, map_add]
  | single j c =>
      rw [emb, AddMonoidAlgebra.mapDomainRingHom_apply, AddMonoidAlgebra.mapDomain_single, wd_single,
        wd_single, AddMonoidAlgebra.mapDomainRingHom_apply, AddMonoidAlgebra.mapDomain_single]
      rfl

theorem DQ_map_emb (w : ℤ × ℤ →+ ℤ) (f : ℤ →+ ℤ × ℤ) (F : PowerSeries L) :
    DQ w (PowerSeries.map (emb f) F) = PowerSeries.map (emb f) (DQ (w.comp f) F) := by
  ext n : 1; simp [wd_emb]

theorem wd_congr {G : Type*} [AddCommGroup G] {w w' : G →+ ℤ} (h : ∀ g, w g = w' g)
    (x : AddMonoidAlgebra ℚ G) : wd w x = wd w' x := by
  rw [AddMonoidHom.ext h]

theorem wd_zero_hom {G : Type*} [AddCommGroup G] (x : AddMonoidAlgebra ℚ G) : wd 0 x = 0 := by
  induction x using AddMonoidAlgebra.induction_linear with
  | zero => exact wd_zero _
  | add x y hx hy => rw [wd_add, hx, hy, add_zero]
  | single j c =>
    rw [wd_single, AddMonoidHom.zero_apply, Int.cast_zero, zero_mul, AddMonoidAlgebra.single_zero]

theorem wd_neg_hom {G : Type*} [AddCommGroup G] (w : G →+ ℤ) (x : AddMonoidAlgebra ℚ G) :
    wd (-w) x = -wd w x := by
  induction x using AddMonoidAlgebra.induction_linear with
  | zero => rw [wd_zero, wd_zero, neg_zero]
  | add x y hx hy => rw [wd_add, hx, hy, wd_add, neg_add]
  | single j c => rw [wd_single, wd_single, ← AddMonoidAlgebra.single_neg]; congr 1; simp

theorem DQ_congr {G : Type*} [AddCommGroup G] {w w' : G →+ ℤ} (h : ∀ g, w g = w' g)
    (F : PowerSeries (AddMonoidAlgebra ℚ G)) : DQ w F = DQ w' F := by
  rw [AddMonoidHom.ext h]

theorem DQ_zero_hom {G : Type*} [AddCommGroup G] (F : PowerSeries (AddMonoidAlgebra ℚ G)) :
    DQ 0 F = 0 := by
  ext n : 1; simp [wd_zero_hom]

theorem DQ_neg_hom {G : Type*} [AddCommGroup G] (w : G →+ ℤ) (F : PowerSeries (AddMonoidAlgebra ℚ G)) :
    DQ (-w) F = -DQ w F := by
  ext n : 1; simp [wd_neg_hom]

/-- The `b`-degree. -/
abbrev wb : ℤ × ℤ →+ ℤ := AddMonoidHom.snd ℤ ℤ

theorem DQ_C_mon2 : DQ wb (PowerSeries.C (mon2 (0, 1))) = PowerSeries.C (mon2 (0, 1)) := by
  ext n : 1
  simp only [coeff_DQ, coeff_C]
  split_ifs
  · rw [mon2, wd_single]; simp
  · exact wd_zero _

/-! ## `Ψ(1) = 0` -/

/-- `a ↦ 1`. -/
abbrev ev1L : L →+* L := embL 0

theorem embL_mono (g : ℤ →+ ℤ) (j : ℤ) : embL g (mono j) = mono (g j) := by
  rw [embL, mono, mono, AddMonoidAlgebra.mapDomainRingHom_apply, AddMonoidAlgebra.mapDomain_single]

theorem embL_negSign (g : ℤ →+ ℤ) (j : ℤ) : embL g (negSign j) = negSign j := by
  simp [negSign]

theorem pentExp_one_sub (j : ℤ) : pentExp (1 - j) = pentExp j := by
  have h1 := two_mul_cast_pentExp j
  have h2 := two_mul_cast_pentExp (1 - j)
  have : (1 - j) * (1 - j - 1) = j * (j - 1) := by ring
  omega

theorem ev_negSign_mono (j : ℤ) : ev1L (negSign j * mono j) = negSign j := by
  rw [map_mul, embL_negSign, embL_mono]; simp [mono_zero]

theorem ev_Psi : PowerSeries.map ev1L Psi = 0 := by
  ext n : 1
  rw [Psi, lat_map, coeff_lat, map_zero]
  refine Finset.sum_involution (fun j _ => 1 - j) ?_ ?_ ?_ ?_
  · intro j _
    simp only [ev_negSign_mono]
    rw [negSign_eq, negSign_eq]
    split_ifs <;> first | ring1 | (exfalso; omega)
  · intro j _ _; simp only; omega
  · intro j hj
    rw [mem_fib hbox_pent] at hj ⊢
    rw [pentExp_one_sub]; exact hj
  · intro j _; ring

/-! ## The diagonal derivative -/

/-- `a ↦ a²`. -/
def dbl : ℤ →+ ℤ := AddMonoidHom.id ℤ + AddMonoidHom.id ℤ

theorem DQ_fa (F : PowerSeries L) : DQ wb (PowerSeries.map (emb fa) F) = 0 := by
  rw [DQ_map_emb, DQ_congr (w' := 0) (fun g => by simp [fa]), DQ_zero_hom, map_zero]

theorem DQ_fb (F : PowerSeries L) :
    DQ wb (PowerSeries.map (emb fb) F) = PowerSeries.map (emb fb) (DQ wa F) := by
  rw [DQ_map_emb, DQ_congr (w' := wa) (fun g => by simp [fb])]

theorem DQ_fab (F : PowerSeries L) :
    DQ wb (PowerSeries.map (emb fab) F) = PowerSeries.map (emb fab) (DQ wa F) := by
  rw [DQ_map_emb, DQ_congr (w' := wa) (fun g => by simp)]

theorem DQ_fq (F : PowerSeries L) :
    DQ wb (PowerSeries.map (emb fq) F) = -PowerSeries.map (emb fq) (DQ wa F) := by
  rw [DQ_map_emb, DQ_congr (w' := -wa) (fun g => by simp), DQ_neg_hom, map_neg]

theorem diag_fa (F : PowerSeries L) : PowerSeries.map diag (PowerSeries.map (emb fa) F) = F := by
  rw [map_diag_map_emb, map_embL_id _ (fun j => by simp [dg])]

theorem diag_fb (F : PowerSeries L) : PowerSeries.map diag (PowerSeries.map (emb fb) F) = F := by
  rw [map_diag_map_emb, map_embL_id _ (fun j => by simp [dg])]

theorem diag_fab (F : PowerSeries L) :
    PowerSeries.map diag (PowerSeries.map (emb fab) F) = PowerSeries.map (embL dbl) F := by
  have : dg.comp fab = dbl := by ext; simp [dg, dbl]
  rw [map_diag_map_emb, this]

theorem diag_fq (F : PowerSeries L) :
    PowerSeries.map diag (PowerSeries.map (emb fq) F) = PowerSeries.map ev1L F := by
  have : dg.comp fq = 0 := by ext; simp [dg]
  rw [map_diag_map_emb, this]

theorem DQ_one {G : Type*} [AddCommGroup G] (w : G →+ ℤ) :
    DQ w (1 : PowerSeries (AddMonoidAlgebra ℚ G)) = 0 := by
  ext n : 1; rw [coeff_DQ, coeff_one]; split_ifs
  · exact wd_one w
  · exact wd_zero w

theorem DQ_two {G : Type*} [AddCommGroup G] (w : G →+ ℤ) :
    DQ w (2 : PowerSeries (AddMonoidAlgebra ℚ G)) = 0 := by
  rw [show (2 : PowerSeries (AddMonoidAlgebra ℚ G)) = 1 + 1 by norm_num, DQ_add, DQ_one, add_zero]

theorem diag_C_mon2 : PowerSeries.map diag (PowerSeries.C (mon2 (0, 1))) = PowerSeries.C (mono 1) := by
  rw [PowerSeries.map_C, diag, mon2, mono, AddMonoidAlgebra.mapDomainRingHom_apply,
    AddMonoidAlgebra.mapDomain_single]
  simp [dg]

/-- **The diagonal identity**: `D(Ψ²)·2G - Ψ²·D(2G) = -κ a Ψ(a²) J`, `J = (DΨ)(1)`. -/
theorem diag_identity :
    DQ wa (Psi * Psi) * (2 * Gser) - Psi * Psi * DQ wa (2 * Gser) =
      -(kap * (PowerSeries.C (mono 1) *
        (PowerSeries.map (embL dbl) Psi * PowerSeries.map ev1L (DQ wa Psi)))) := by
  have h := congrArg (fun F => PowerSeries.map diag (DQ wb F)) two_var
  simp only [DQ_sub, DQ_mul, DQ_fa, DQ_fb, DQ_fab, DQ_fq, DQ_C_mon2, map_sub, map_mul, map_add,
    map_neg, map_zero, diag_fa, diag_fb, diag_fab, diag_fq, diag_C_mon2, ev_Psi, DQ_two] at h ⊢
  linear_combination h

end

end VOA.DeligneAudit.DeligneCharacter.D4Wp
