import VOA.Classification.COne.OrbC2bOcta

/-! # Finite Klein four calculations inside the standard permutation group -/
set_option maxSynthPendingDepth 3
set_option maxRecDepth 4096
namespace VOA.Classification.COne.OrbC2d
open VOA OrbC2b Equiv Equiv.Perm

def kleinPermFun : DihedralGroup 2 → Perm (Fin 4)
  | .r i => if i = 0 then 1 else halfZ
  | .sr i => if i = 0 then halfX else halfY

def kleinPerm : DihedralGroup 2 →* Perm (Fin 4) where
  toFun := kleinPermFun
  map_one' := by decide +kernel
  map_mul' := by decide +kernel

theorem kleinPerm_injective : Function.Injective kleinPerm := by decide +kernel

theorem kleinPerm_even (d : DihedralGroup 2) : kleinPerm d ∈ alternatingGroup (Fin 4) := by
  have h : ∀ d : DihedralGroup 2, (kleinPerm d).sign = 1 := by decide +kernel
  exact mem_alternatingGroup.mpr (h d)

theorem kleinPerm_normal (s : Perm (Fin 4)) (d : DihedralGroup 2) :
    ∃ e : DihedralGroup 2, s * kleinPerm d * s⁻¹ = kleinPerm e := by
  have h : ∀ (s : Perm (Fin 4)) (d : DihedralGroup 2),
      ∃ e : DihedralGroup 2, s * kleinPerm d * s⁻¹ = kleinPerm e := by decide +kernel
  exact h s d

theorem kleinPerm_values (d : DihedralGroup 2) :
    kleinPerm d = 1 ∨ kleinPerm d = halfX ∨ kleinPerm d = halfY ∨ kleinPerm d = halfZ := by
  have h : ∀ d : DihedralGroup 2,
      kleinPerm d = 1 ∨ kleinPerm d = halfX ∨ kleinPerm d = halfY ∨ kleinPerm d = halfZ := by
    decide +kernel
  exact h d

/-- Any permutation of the three nonidentity Klein elements is induced by S₄. -/
theorem kleinPerm_aut_realized (f : DihedralGroup 2 ≃* DihedralGroup 2) :
    ∃ s : Perm (Fin 4), ∀ d, kleinPerm (f d) = s * kleinPerm d * s⁻¹ := by
  have h : ∀ f : Equiv.Perm (DihedralGroup 2), f 1 = 1 →
      ∃ s : Perm (Fin 4), ∀ d, kleinPerm (f d) = s * kleinPerm d * s⁻¹ := by
    decide +kernel
  exact h f.toEquiv f.map_one

/-- Every even permutation on four letters is a product of two elements
whose cubes are one. This will force every A₄ → S₄ map to have even image. -/
theorem even_cube_factorization (s : alternatingGroup (Fin 4)) :
    ∃ a b : alternatingGroup (Fin 4), a ^ 3 = 1 ∧ b ^ 3 = 1 ∧ s = a * b := by
  have h : ∀ s : alternatingGroup (Fin 4),
      ∃ a b : alternatingGroup (Fin 4), a ^ 3 = 1 ∧ b ^ 3 = 1 ∧ s = a * b := by
    decide +kernel
  exact h s

end VOA.Classification.COne.OrbC2d
