/-
Copyright (c) 2026 Leonardo Rastelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo Rastelli
-/
import VOA.DeligneAudit.DeligneSectorWeyl
import VOA.DeligneAudit.A2SectorB8

/-!
# `M_m` is a `B_m`-module (type-generic)

The power sums act on `δ_{c₀}` through a Cartan loop operator `h_θ ⊗ t^r` with `θ(h_θ) ≠ 0`, and
generate `B_m` (Newton, fundamental theorem): `M_m = U(g[t])·δ_{c₀}` is a `B_m`-submodule.
-/

namespace VOA.DeligneAudit.DeligneSector

open MvPolynomial VOA.DeligneAudit.SectorLoop VOA.DeligneAudit.SectorFiber
open VOA.DeligneAudit.SectorFiberModule VOA.QuadraticCurrentFunctionalCarrier
open VOA.DeligneAudit.A2 (psumS esymmS psumS_mem esymmS_mem)

noncomputable section

variable (S : DeligneSectorData)

theorem applyWord_smul (m : ℕ) (s : SymAlg (K := ℂ) m) :
    ∀ (l : List (Fin S.n × ℕ)) (v : TPs S m),
      applyWord S.f m l (s • v) = s • applyWord S.f m l v
  | [], _ => rfl
  | (xs :: l), v => by
      change loopOp S.f m xs.1 xs.2 (applyWord S.f m l (s • v)) = _
      rw [applyWord_smul m s l v, loopOp_smul]
      rfl

theorem applyWord_append (m : ℕ) (l l' : List (Fin S.n × ℕ))
    (v : TPs S m) :
    applyWord S.f m (l ++ l') v =
      applyWord S.f m l (applyWord S.f m l' v) := by
  induction l with
  | nil => rfl
  | cons xs l ih =>
      change loopOp _ _ _ _ (applyWord _ _ (l ++ l') v) = _
      rw [ih]
      rfl

/-- The symmetric polynomials preserving `M_m`. -/
def stab (m : ℕ) : Subalgebra ℂ (SymAlg (K := ℂ) m) where
  carrier := {s | ∀ x ∈ Mspace S.f m S.c₀, s • x ∈ Mspace S.f m S.c₀}
  mul_mem' {s t} hs ht x hx := by rw [mul_smul]; exact hs _ (ht x hx)
  add_mem' {s t} hs ht x hx := by rw [add_smul]; exact Submodule.add_mem _ (hs x hx) (ht x hx)
  algebraMap_mem' c x hx := by
    rw [algebraMap_smul]
    exact Submodule.smul_mem _ c hx

theorem psumS_mem_stab (m r : ℕ) : psumS m r ∈ stab S m := by
  intro x hx
  have hθ : ((S.thetaH S.hθ : ℕ) : ℂ) ≠ 0 := by exact_mod_cast S.hθ_ne
  induction hx using Submodule.span_induction with
  | mem v hv =>
      obtain ⟨l, rfl⟩ := hv
      rw [← applyWord_smul]
      have h := loopOp_cartan_deltaVec S m S.hθ S.hθ_cartan r
      have h2 : psumS m r • deltaVec (K := ℂ) m S.c₀ =
          ((S.thetaH S.hθ : ℕ) : ℂ)⁻¹ • loopOp S.f m S.hθ r (deltaVec m S.c₀) := by
        rw [h, smul_smul, inv_mul_cancel₀ hθ, one_smul]
      rw [h2, ← algebraMap_smul (SymAlg (K := ℂ) m), applyWord_smul, algebraMap_smul]
      refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨l ++ [(S.hθ, r)], ?_⟩)
      show applyWord S.f m (l ++ [(S.hθ, r)]) (deltaVec m S.c₀) = _
      rw [applyWord_append]
      rfl
  | zero => rw [smul_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [smul_add]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [smul_comm]; exact Submodule.smul_mem _ c ha

theorem esymmS_mem_stab (m : ℕ) : ∀ k, esymmS m k ∈ stab S m := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · have : esymmS m 0 = 1 := Subtype.ext (by simp [esymmS])
        rw [this]; exact Subalgebra.one_mem _
      · -- Newton: k e_k = (-1)^(k+1) Σ_{a<k} (-1)^a e_a p_{k-a}
        have hN := mul_esymm_eq_sum (Fin (m + 0)) ℂ k
        have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
        have heq : esymmS m k = (k : ℂ)⁻¹ • (((-1 : ℂ) ^ (k + 1)) •
            ∑ a ∈ Finset.antidiagonal k with a.1 < k,
              ((-1 : ℂ) ^ a.1) • (esymmS m a.1 * psumS m a.2)) := by
          apply Subtype.ext
          simp only [Subalgebra.coe_smul, Subalgebra.coe_mul, esymmS, psumS,
            AddSubmonoidClass.coe_finsetSum]
          rw [eq_inv_smul_iff₀ hkC]
          simp only [smul_eq_C_mul, map_pow, map_neg, map_one, Finset.mul_sum] at hN ⊢
          rw [show (MvPolynomial.C (k : ℂ) : MvPolynomial (Fin (m + 0)) ℂ) = (k : MvPolynomial _ ℂ) by
            simp, hN]
          refine Finset.sum_congr rfl fun a _ => ?_
          ring
        rw [heq]
        have hterm : ∀ a ∈ (Finset.antidiagonal k).filter (fun a => a.1 < k),
            ((-1 : ℂ) ^ a.1) • (esymmS m a.1 * psumS m a.2) ∈ stab S m := by
          intro a ha
          have h1 : esymmS m a.1 * psumS m a.2 ∈ stab S m :=
            (stab S m).mul_mem (ih a.1 (Finset.mem_filter.mp ha).2) (psumS_mem_stab S m a.2)
          exact (stab S m).smul_mem h1 _
        have hsum := (stab S m).sum_mem hterm
        exact (stab S m).smul_mem ((stab S m).smul_mem hsum ((-1 : ℂ) ^ (k + 1))) ((k : ℂ)⁻¹)

theorem stab_eq_top (m : ℕ) : stab S m = ⊤ := by
  rw [eq_top_iff]
  intro s _
  obtain ⟨p, rfl⟩ := esymmAlgHom_surjective (σ := Fin (m + 0)) (n := m) ℂ (by simp) s
  have hr : esymmAlgHom (Fin (m + 0)) ℂ m p ∈ (aeval fun i : Fin m =>
      (⟨esymm (Fin (m + 0)) ℂ (i + 1), esymm_isSymmetric _ _ _⟩ : SymAlg (K := ℂ) m)).range :=
    ⟨p, rfl⟩
  rw [aeval_range] at hr
  refine Algebra.adjoin_le ?_ hr
  rintro _ ⟨i, rfl⟩
  exact esymmS_mem_stab S m (i + 1)

/-- **`M_m` is stable under the symmetric polynomials.** -/
theorem smul_mem_Mspace (m : ℕ) (s : SymAlg (K := ℂ) m)
    {x : TPs S m} (hx : x ∈ Mspace S.f m S.c₀) :
    s • x ∈ Mspace S.f m S.c₀ := by
  have : s ∈ stab S m := by rw [stab_eq_top S]; trivial
  exact this x hx

/-- `M_m` as a `B_m`-submodule. -/
def MspaceR (m : ℕ) : Submodule (SymAlg (K := ℂ) m) (TPs S m) where
  carrier := Mspace S.f m S.c₀
  zero_mem' := Submodule.zero_mem _
  add_mem' := Submodule.add_mem _
  smul_mem' s _ hx := smul_mem_Mspace S m s hx

theorem torsionFree (m : ℕ) (s : SymAlg (K := ℂ) m)
    (x : TPs S m) (hs : s ≠ 0) (h : s • x = 0) : x = 0 := by
  funext t
  have ht := congrFun h t
  rw [smul_apply_sym] at ht
  have hs' : (s : MvPolynomial (Fin (m + 0)) ℂ) ≠ 0 := fun h0 => hs (Subtype.ext h0)
  exact (mul_eq_zero.mp ht).resolve_left hs'


end

end VOA.DeligneAudit.DeligneSector
