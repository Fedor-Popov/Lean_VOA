/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import Mathlib

/-!
# Lowering saturation and horizontal highest vectors

Saturation records eventual entry into a lowering-stable subspace.
An operator with a nilpotent adjoint lowering string preserves this
saturation. The exact sl2 ladder then forces highest vectors with
weights outside the nonnegative integers into the original subspace.
No irreducibility or finite-dimensionality is used.
-/

namespace VOA.HorizontalSaturation
noncomputable section
open Module
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Once a lowering power enters an invariant subspace, every higher power remains there. -/
private theorem power_mem_above (F : End ℂ V) (S : Submodule ℂ V)
    (hF : ∀ v∈S,F v∈S) {v : V} {n m : ℕ} (h : (F^n) v∈S) (hn : n ≤ m) :
    (F^m) v∈S := by
  obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [pow_add,Module.End.mul_apply]
  have hh : ∀ d,(F^d) ((F^n) v)∈S := by
    intro d
    induction d with
    | zero => simpa using h
    | succ d ih => simpa only [pow_succ',Module.End.mul_apply] using hF _ ih
  simpa only [← Module.End.mul_apply,← pow_add,Nat.add_comm] using hh d

/-- Saturation consists of vectors whose sufficiently high lowering power
lies in the given lowering-stable subspace. -/
def saturation (F : End ℂ V) (S : Submodule ℂ V) (hF : ∀ v∈S,F v∈S) : Submodule ℂ V where
  carrier := {v | ∃ n : ℕ,(F^n) v∈S}
  zero_mem' := ⟨0,by simp⟩
  add_mem' := by
    rintro v w ⟨n,hn⟩ ⟨m,hm⟩
    refine ⟨n+m,?_⟩
    rw [map_add]
    exact S.add_mem (power_mem_above F S hF hn (by omega))
      (power_mem_above F S hF hm (by omega))
  smul_mem' := by
    rintro c v ⟨n,hn⟩
    exact ⟨n,by rw [map_smul]; exact S.smul_mem c hn⟩

/-- Saturation contains the original subspace. -/
theorem le_saturation (F : End ℂ V) (S : Submodule ℂ V) (hF : ∀ v∈S,F v∈S) :
    S ≤ saturation F S hF := by intro v hv; exact ⟨0,by simpa using hv⟩

/-- A vector enters saturation exactly when its next lowering power does. -/
theorem mem_of_lower_mem (F : End ℂ V) (S : Submodule ℂ V) (hF : ∀ v∈S,F v∈S)
    {v : V} (h : F v∈saturation F S hF) : v∈saturation F S hF := by
  obtain ⟨n,hn⟩ := h
  exact ⟨n+1,by simpa only [pow_succ,Module.End.mul_apply] using hn⟩

/-- If the commutator already preserves saturation, a subspace-preserving
operator itself preserves saturation. The proof descends the power witness. -/
theorem stable_of_commutator (F X : End ℂ V) (S : Submodule ℂ V)
    (hF : ∀ v∈S,F v∈S) (hX : ∀ v∈S,X v∈S)
    (hC : ∀ v∈saturation F S hF,⁅F,X⁆ v∈saturation F S hF) :
    ∀ v∈saturation F S hF,X v∈saturation F S hF := by
  rintro v ⟨n,hn⟩
  induction n generalizing v with
  | zero => exact le_saturation F S hF (hX v (by simpa using hn))
  | succ n ih =>
      have hv : v∈saturation F S hF := ⟨n+1,hn⟩
      have hv' : (F^n) (F v)∈S := by simpa only [pow_succ,Module.End.mul_apply] using hn
      apply mem_of_lower_mem F S hF
      have he : F (X v)=X (F v)+⁅F,X⁆ v := by simp [Ring.lie_def]
      rw [he]
      exact (saturation F S hF).add_mem (ih _ hv') (hC _ hv)

/-- A nilpotent adjoint string of length three is enough to preserve
saturation; no nilpotence on the original vector space is assumed. -/
theorem stable_of_ad_cube (F X : End ℂ V) (S : Submodule ℂ V)
    (hF : ∀ v∈S,F v∈S) (hX : ∀ v∈S,X v∈S)
    (h3 : ⁅F,⁅F,⁅F,X⁆⁆⁆=0) :
    ∀ v∈saturation F S hF,X v∈saturation F S hF := by
  have hC (Y : End ℂ V) (hY : ∀ v∈S,Y v∈S) : ∀ v∈S,⁅F,Y⁆ v∈S := by
    intro v hv
    simp only [Ring.lie_def,LinearMap.sub_apply,Module.End.mul_apply]
    exact S.sub_mem (hF _ (hY _ hv)) (hY _ (hF _ hv))
  apply stable_of_commutator F X S hF hX
  apply stable_of_commutator F ⁅F,X⁆ S hF (hC X hX)
  apply stable_of_commutator F ⁅F,⁅F,X⁆⁆ S hF (hC _ (hC X hX))
  intro v hv
  rw [h3,LinearMap.zero_apply]
  exact Submodule.zero_mem _
/-- Evaluation converts an actual operator commutator to its pointwise identity. -/
private theorem bracket_apply (E F G : End ℂ V) (h : ⁅E,F⁆=G) (v : V) :
    E (F v)=F (E v)+G v := by
  have hh := LinearMap.congr_fun h v
  simp only [Ring.lie_def,LinearMap.sub_apply,Module.End.mul_apply] at hh
  rw [sub_eq_iff_eq_add] at hh
  simpa only [add_comm] using hh

/-- A Cartan commutator gives exact weights on all powers of one lowering operator. -/
private theorem weight_power (H F : End ℂ V)
    (h : ⁅H,F⁆=(-2 : ℂ) • F) (v : V) (z : ℂ) (hv : H v=z • v) (n : ℕ) :
    H ((F^n) v)=(z-2*n) • (F^n) v := by
  induction n with
  | zero => simpa using hv
  | succ n ih =>
      rw [pow_succ',Module.End.mul_apply,bracket_apply H F _ h,ih,map_smul,LinearMap.smul_apply]
      push_cast
      module

/-- The sl2 ladder with an arbitrary initial raising defect, rather than
assuming that the initial vector is killed by the raising operator. -/
theorem raising_power_succ (E F H : End ℂ V)
    (hef : ⁅E,F⁆=H) (hhf : ⁅H,F⁆=(-2 : ℂ) • F)
    (v : V) (z : ℂ) (hv : H v=z • v) (n : ℕ) :
    E ((F^(n+1)) v)=(F^(n+1)) (E v)+((n+1 : ℂ)*(z-n)) • (F^n) v := by
  induction n with
  | zero => simpa [hv] using bracket_apply E F H hef v
  | succ n ih =>
      rw [pow_succ',Module.End.mul_apply,bracket_apply E F H hef,ih,map_add,map_smul,
        weight_power H F hhf v z hv]
      simp only [← Module.End.mul_apply,← mul_assoc,← pow_succ']
      push_cast
      module

/-- A highest vector whose horizontal weight avoids all nonnegative
integers cannot survive in a quotient where lowering is locally nilpotent.
This is subspace containment, with no irreducibility assumption. -/
theorem highest_mem_of_saturation (E F H : End ℂ V) (S : Submodule ℂ V)
    (hF : ∀ v∈S,F v∈S) (hE : ∀ v∈S,E v∈S)
    (hef : ⁅E,F⁆=H) (hhf : ⁅H,F⁆=(-2 : ℂ) • F)
    (v : V) (z : ℂ) (hz : ∀ n : ℕ,z-(n : ℂ)≠0)
    (hv : H v=z • v) (he : E v=0) (hs : v∈saturation F S hF) : v∈S := by
  obtain ⟨n,hn⟩ := hs
  induction n with
  | zero => simpa using hn
  | succ n ih =>
      apply ih
      have hr := hE _ hn
      rw [raising_power_succ E F H hef hhf v z hv n,he,map_zero,zero_add] at hr
      exact (S.smul_mem_iff (mul_ne_zero (by exact_mod_cast Nat.succ_ne_zero n) (hz n))).mp hr
end
end VOA.HorizontalSaturation
