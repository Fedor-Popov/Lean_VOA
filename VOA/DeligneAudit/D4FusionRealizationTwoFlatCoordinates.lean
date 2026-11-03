/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.D4FusionRealizationTwoCoordinates
import Mathlib.Logic.Equiv.Fin.Basic

/-! The numerical certificate's index i*(n+1)+j is an explicit equivalence
of the actual tensor coordinates, not an assumed matrix identification. -/
namespace VOA.DeligneAudit.D4Two

noncomputable section

def siteFlat (n : ℕ) : SiteIndex n ≃ Fin (n + 1) where
  toFun := Sum.elim Fin.castSucc (fun _ => Fin.last n)
  invFun i := if h : i.val < n then Sum.inl ⟨i.val, h⟩ else Sum.inr ()
  left_inv i := by
    cases i with
    | inl i => simp [i.isLt]
    | inr i => cases i; simp
  right_inv i := by
    dsimp only
    split_ifs with hi
    · rfl
    · apply Fin.ext
      change n = i.val
      omega

@[simp] theorem siteFlat_inl (n : ℕ) (i : Fin n) :
    (siteFlat n (Sum.inl i)).val = i.val := rfl

@[simp] theorem siteFlat_inr (n : ℕ) :
    (siteFlat n (Sum.inr ())).val = n := rfl

def pairFlat (n : ℕ) : PairIndex n ≃ Fin ((n + 1) * (n + 1)) :=
  (Equiv.prodCongr (siteFlat n) (siteFlat n)).trans finProdFinEquiv

theorem pairFlat_val (n : ℕ) (p : PairIndex n) :
    (pairFlat n p).val = (siteFlat n p.1).val * (n + 1) + (siteFlat n p.2).val := by
  dsimp [pairFlat, finProdFinEquiv]
  ac_rfl

/-- Flat coordinates of the genuine two-site tensor space. -/
def flatCoordinates (n : ℕ) :
    D1TensorG.Space n 2 ≃ₗ[ℂ] (Fin ((n + 1) * (n + 1)) → ℂ) :=
  (coordinates n).trans (LinearEquiv.funCongrLeft ℂ ℂ (pairFlat n).symm)

@[simp] theorem flatCoordinates_at_pair (n : ℕ) (v : D1TensorG.Space n 2)
    (p : PairIndex n) : flatCoordinates n v (pairFlat n p) = coordinates n v p := by
  change coordinates n v ((pairFlat n).symm (pairFlat n p)) = _
  rw [Equiv.symm_apply_apply]

end
end VOA.DeligneAudit.D4Two

#print axioms VOA.DeligneAudit.D4Two.flatCoordinates_at_pair
