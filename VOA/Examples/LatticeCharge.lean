/-
Copyright (c) 2026 Leonardo Rastelli and Fedor K. Popov. All rights reserved.
Released under the Apache 2.0 license; see the LICENSE file.
Authors: Leonardo Rastelli, Fedor K. Popov
-/
import VOA.Examples.LatticeGenInstance
import VOA.Modules.FiniteGenerationProof
import VOA.Modules.ModuleRestrict

/-!
# Charge additivity for the lattice vertex operators

Every vertex operator of `V_L` **shifts the charge sector by its own charge**.  This is the
input the charge-zero sub-VOA needs, and thence — by `VOASubalgebra.restrictWeakModule` — the
charged Fock modules `F_α` as Heisenberg modules, with the module Jacobi identity *inherited*
from the proved VOA Jacobi identity rather than re-established.

## The statement

With `chargeSec γ := range (mkEα γ)` (the Fock factor at `e^γ`), a formal distribution `f`
**shifts charge by `α`** when `f k` maps `chargeSec β` into `chargeSec (α+β)` for every `β, k`
(`ShiftsCharge`).  The two generators behave as expected and the property is stable under
everything `YwordLatGenF` builds with:

* `alphaLatGen` shifts by `0` — the boson current preserves each sector (`rTensor` acts on the
  Fock factor; the momentum term is a scalar by `zGradeOpGen_latStateGen`);
* `Yeαvec α` shifts by `α` — immediate from `Yeαvec_tmul`;
* `ShiftsCharge` is closed under `deriv`, scalar multiples, and `nprod` (composition of
  coefficients in either order lands in the same sector, and `finsum_induction` carries it
  through the sum).

Hence `YwordLatGen l α` shifts by `α` for every word `l`, by induction along `YwordLatGenF`.

## Status

Proved, `sorry`-free.  The transport from word states to all of `V_L` is `YfullGen_shiftsCharge`;
the charge-zero sub-VOA is `chargeZeroSubVOA` and the restricted module is
`latticeAsHeisenbergModule`.
-/

namespace VOA.LatGen

open HeisenbergN VOA.IntegralLattice

variable (L : IntegralLattice)

/-! ## Charge sectors -/

/-- The **charge-`γ` sector** of `V_L`: the Fock factor sitting at `e^γ`. -/
noncomputable def chargeSec (γ : L.carrier) : Submodule ℂ (LatModuleGen L) :=
  LinearMap.range (mkEα L γ)

theorem mem_chargeSec (γ : L.carrier) (p : FockN (rank L)) :
    latStateGen L p γ ∈ chargeSec L γ := ⟨p, rfl⟩

/-- A distribution **shifts charge by `α`** if every coefficient maps the charge-`β` sector into
the charge-`α+β` sector. -/
def ShiftsCharge (f : FormalDist (Module.End ℂ (LatModuleGen L))) (α : L.carrier) : Prop :=
  ∀ (β : L.carrier) (k : ℤ), ∀ x ∈ chargeSec L β, f k x ∈ chargeSec L (α + β)

/-! ## The two generators -/

/-- **The boson current preserves each charge sector** (shift by `0`). -/
theorem alphaLatGen_shiftsCharge (a : Fin (rank L)) :
    ShiftsCharge L (alphaLatGen L a) 0 := by
  rintro β k _ ⟨p, rfl⟩
  rw [zero_add]
  show alphaLatGen L a k (latStateGen L p β) ∈ _
  rw [alphaLatGen_apply, LinearMap.add_apply]
  refine Submodule.add_mem _ ?_ ?_
  · show LinearMap.rTensor _ (currentN (rank L) 1 a k) (latStateGen L p β) ∈ _
    rw [latStateGen, LinearMap.rTensor_tmul]
    exact mem_chargeSec L β _
  · by_cases hk : k = -1
    · rw [if_pos hk, zGradeOpGen_latStateGen]
      exact Submodule.smul_mem _ _ (mem_chargeSec L β p)
    · rw [if_neg hk]; simp

/-- **The charged operator shifts the charge sector by `α`.** -/
theorem Yeαvec_shiftsCharge (α : L.carrier) :
    ShiftsCharge L (Yeαvec L α) α := by
  rintro β k _ ⟨p, rfl⟩
  show Yeαvec L α k (latStateGen L p β) ∈ _
  rw [Yeαvec_tmul]
  exact Submodule.smul_mem _ _ (mem_chargeSec L (α + β) _)

/-! ## Stability under the field constructors -/

theorem ShiftsCharge.deriv {f : FormalDist (Module.End ℂ (LatModuleGen L))} {α : L.carrier}
    (hf : ShiftsCharge L f α) : ShiftsCharge L (VOA.deriv f) α := by
  intro β k x hx
  rw [VOA.deriv_apply]
  exact zsmul_mem (hf β (k + 1) x hx) _

theorem ShiftsCharge.smul {f : FormalDist (Module.End ℂ (LatModuleGen L))} {α : L.carrier}
    (c : ℂ) (hf : ShiftsCharge L f α) : ShiftsCharge L (c • f) α := by
  intro β k x hx
  exact Submodule.smul_mem _ _ (hf β k x hx)

theorem ShiftsCharge.iterate_deriv {f : FormalDist (Module.End ℂ (LatModuleGen L))}
    {α : L.carrier} (hf : ShiftsCharge L f α) (i : ℕ) :
    ShiftsCharge L (VOA.deriv^[i] f) α := by
  induction i with
  | zero => simpa using hf
  | succ i ih => rw [Function.iterate_succ_apply']; exact ih.deriv L

/-- **`nprod` composes charge shifts**: a charge-`α` field normal-ordered against a charge-`α'`
field shifts by `α + α'`.  Each `normalOrdered` term is a composition of coefficients — in either
order — so it lands in the right sector, and `finsum_induction` carries that through the sum. -/
theorem ShiftsCharge.nprod {a b : FormalDist (Module.End ℂ (LatModuleGen L))}
    {α α' : L.carrier} (ha : IsField a) (hb : IsField b)
    (hA : ShiftsCharge L a α) (hB : ShiftsCharge L b α') :
    ShiftsCharge L (VOA.nprod ha hb) (α + α') := by
  intro β k x hx
  rw [VOA.nprod_apply]
  refine finsum_induction (fun y => y ∈ chargeSec L (α + α' + β)) (Submodule.zero_mem _)
    (fun _ _ => Submodule.add_mem _) (fun m => ?_)
  rw [normalOrdered_apply]
  by_cases hm : 0 ≤ m
  · rw [if_pos hm]
    show a m (b (k - m) x) ∈ _
    have h1 : b (k - m) x ∈ chargeSec L (α' + β) := hB β (k - m) x hx
    have h2 := hA (α' + β) m _ h1
    rwa [← add_assoc] at h2
  · rw [if_neg hm]
    show b (k - m) (a m x) ∈ _
    have h1 : a m x ∈ chargeSec L (α + β) := hA β m x hx
    have h2 := hB (α + β) (k - m) _ h1
    rwa [show α' + (α + β) = α + α' + β from by abel] at h2

/-! ## Word fields -/

/-- **Every lattice word field shifts charge by its charge.**  Induction along
`YwordLatGenF`: the base case is `Yeαvec`, and each cons is an `nprod` with the charge-`0`
generator field. -/
theorem YwordLatGen_shiftsCharge (l : List (ℕ × Fin (rank L))) (α : L.carrier) :
    ShiftsCharge L (YwordLatGen L l α) α := by
  induction l with
  | nil => exact Yeαvec_shiftsCharge L α
  | cons ia rest ih =>
      have hgen : ShiftsCharge L (genFieldLatGen L ia.2 ia.1) 0 := by
        unfold genFieldLatGen
        exact ((alphaLatGen_shiftsCharge L ia.2).iterate_deriv L ia.1).smul L _
      have := ShiftsCharge.nprod L (genFieldLatGen_isField L ia.2 ia.1)
        (YwordLatGen_isField L rest α) hgen ih
      rwa [zero_add] at this

/-! ## `ShiftsCharge` is closed under the linear structure -/

theorem ShiftsCharge.zero (α : L.carrier) :
    ShiftsCharge L (0 : FormalDist (Module.End ℂ (LatModuleGen L))) α := by
  intro β k x _
  show (0 : Module.End ℂ (LatModuleGen L)) x ∈ _
  simp

theorem ShiftsCharge.add {f g : FormalDist (Module.End ℂ (LatModuleGen L))} {α : L.carrier}
    (hf : ShiftsCharge L f α) (hg : ShiftsCharge L g α) : ShiftsCharge L (f + g) α := by
  intro β k x hx
  exact Submodule.add_mem _ (hf β k x hx) (hg β k x hx)

/-! ## Word states live in their charge sector -/

theorem wordStateLatGen_mem_chargeSec (l : List (ℕ × Fin (rank L))) (α : L.carrier) :
    wordStateLatGen L l α ∈ chargeSec L α := by
  induction l with
  | nil => exact mem_chargeSec L α _
  | cons ia rest ih =>
      rw [wordStateLatGen]
      obtain ⟨p, hp⟩ := ih
      rw [← hp]
      show LinearMap.rTensor _ _ (latStateGen L p α) ∈ _
      rw [latStateGen, LinearMap.rTensor_tmul]
      exact mem_chargeSec L α _

/-! ## Transport to all of `V_L`

`YfullGen` is `.choose`-defined, so `YfullGen_word` is the only bridge to explicit formulas.
The charge-`α` sector is spanned by the charge-`α` word states, so linearity of `YfullGen`
carries `ShiftsCharge` from the word states to the whole sector. -/

/-- The charge-`α` sector is spanned by the charge-`α` word states.  Mirrors the argument of
`wordStateLatGen_span`, but *within* a fixed charge sector: expand the Fock factor over its
monomial basis, and each monomial is a word state by `wordStateLatGen_eq`. -/
theorem chargeSec_le_span_word (α : L.carrier) :
    chargeSec L α ≤ Submodule.span ℂ {x | ∃ l, wordStateLatGen L l α = x} := by
  classical
  set S := Submodule.span ℂ {x | ∃ l, wordStateLatGen L l α = x} with hS
  have hmono : ∀ a : (ℕ × Fin (rank L)) →₀ ℕ,
      (MvPolynomial.monomial a (1 : ℂ)) ⊗ₜ[ℂ] eGen L α ∈ S := by
    intro a
    refine Submodule.subset_span ⟨HeisenbergN.monoWordN a, ?_⟩
    rw [wordStateLatGen_eq, HeisenbergN.wordStateN_monoWordN]
  rintro _ ⟨p, rfl⟩
  show (p ⊗ₜ[ℂ] eGen L α) ∈ S
  rw [← MvPolynomial.support_sum_monomial_coeff p, TensorProduct.sum_tmul]
  refine Submodule.sum_mem _ (fun a _ => ?_)
  rw [show (MvPolynomial.monomial a (MvPolynomial.coeff a p))
        = (MvPolynomial.coeff a p) • MvPolynomial.monomial a (1 : ℂ) from by
      rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one],
    ← TensorProduct.smul_tmul' (MvPolynomial.coeff a p) (MvPolynomial.monomial a (1 : ℂ))
      (eGen L α)]
  exact Submodule.smul_mem _ _ (hmono a)

/-- **Every state of charge `α` gives a vertex operator that shifts charge by `α`.**  This is
the transport of `YwordLatGen_shiftsCharge` across `YfullGen_word`, using that the charge-`α`
sector is spanned by charge-`α` word states and that `YfullGen` is linear. -/
theorem YfullGen_shiftsCharge (hEven : L.Even) (hPos : L.PosDef) (α : L.carrier)
    {u : LatModuleGen L} (hu : u ∈ chargeSec L α) :
    ShiftsCharge L (YfullGen L hEven hPos u) α := by
  refine Submodule.span_induction
    (p := fun y _ => ShiftsCharge L (YfullGen L hEven hPos y) α)
    (fun y hy => ?_) (?_) (fun y z _ _ h1 h2 => ?_) (fun c y _ h => ?_)
    (chargeSec_le_span_word L α hu)
  · obtain ⟨l, hl⟩ := hy
    show ShiftsCharge L (YfullGen L hEven hPos y) α
    rw [← hl, YfullGen_word]
    exact YwordLatGen_shiftsCharge L l α
  · show ShiftsCharge L (YfullGen L hEven hPos 0) α
    rw [map_zero]; exact ShiftsCharge.zero L α
  · show ShiftsCharge L (YfullGen L hEven hPos (y + z)) α
    rw [map_add]; exact (h1 : ShiftsCharge L _ α).add L h2
  · show ShiftsCharge L (YfullGen L hEven hPos (c • y)) α
    rw [map_smul]; exact (h : ShiftsCharge L _ α).smul L c

/-! ## The charge-zero sub-VOA

Three of the four `VOASubalgebra` fields are immediate — the vacuum and `ω` are literally
`mkEα 0 (…)`, and `smul_mem` is `YfullGen_shiftsCharge` at `α = 0`.  The fourth, `graded`, says
the weight-grading projection preserves the charge sector; it holds because
`bigradα (w,α) ≤ chargeSec α` and the charge-zero sector is the supremum of its weight pieces. -/

theorem bigradα_le_chargeSec (w : ℤ) (α : L.carrier) :
    bigradα L (w, α) ≤ chargeSec L α := by
  rw [bigradα]
  rintro _ ⟨p, _, rfl⟩
  exact ⟨p, rfl⟩

theorem latVacuumGen_mem_chargeSec : latVacuumGen L ∈ chargeSec L 0 :=
  mem_chargeSec L 0 _

theorem omegaLatGen_mem_chargeSec : omegaLatGen L ∈ chargeSec L 0 := ⟨_, rfl⟩

/-- **`smul_mem` for the charge-zero sector**: products of charge-zero states are charge-zero. -/
theorem chargeSec_zero_smul_mem (hEven : L.Even) (hPos : L.PosDef)
    {u : LatModuleGen L} (hu : u ∈ chargeSec L 0) (n : ℤ)
    {v : LatModuleGen L} (hv : v ∈ chargeSec L 0) :
    (latticeVOAGen L hEven hPos).smul u n v ∈ chargeSec L 0 := by
  have h := YfullGen_shiftsCharge L hEven hPos 0 hu 0 (-n - 1) v hv
  rwa [add_zero] at h

/-- The charge-zero sector is the supremum of its weight pieces. -/
theorem chargeSec_zero_eq_iSup : chargeSec L 0 = ⨆ w : ℤ, bigradα L (w, 0) := by
  have hb : ∀ w : ℤ, bigradα L (w, 0)
      = (HeisenbergN.gradingZN (rank L) w).map (mkEα L 0) := fun _ => rfl
  simp only [hb]
  rw [← Submodule.map_iSup, HeisenbergN.gradingZN_iSup_eq_top, Submodule.map_top, chargeSec]

/-- **`graded` for the charge-zero sector**: the weight-grading projection preserves it. -/
theorem chargeSec_zero_graded (hEven : L.Even) (hPos : L.PosDef)
    (n : ℤ) {v : LatModuleGen L} (hv : v ∈ chargeSec L 0) :
    piHom (latticeVOAGen L hEven hPos) n v ∈ chargeSec L 0 := by
  classical
  rw [chargeSec_zero_eq_iSup] at hv
  refine Submodule.iSup_induction _ (motive := fun y => piHom (latticeVOAGen L hEven hPos) n y
      ∈ chargeSec L 0) hv ?_ ?_ ?_
  · intro w y hy
    have hgw : y ∈ (latticeVOAGen L hEven hPos).grading w := by
      have := bigradα_le_gradingLatGen L w 0 hy
      rwa [halfNorm_zero L, add_zero] at this
    by_cases hn : n = w
    · subst hn
      rw [piHom_apply, DirectSum.decompose_of_mem _ hgw]
      simpa using bigradα_le_chargeSec L n 0 hy
    · rw [piHom_apply, DirectSum.decompose_of_mem_ne _ hgw (Ne.symm hn)]
      exact Submodule.zero_mem _
  · show piHom (latticeVOAGen L hEven hPos) n 0 ∈ _
    rw [map_zero]; exact Submodule.zero_mem _
  · intro y z hy hz
    show piHom (latticeVOAGen L hEven hPos) n (y + z) ∈ _
    rw [map_add]; exact Submodule.add_mem _ hy hz

/-! ## The charge-zero sub-VOA, and the charged modules

All four fields are available, so the charge-zero sector is a sub-VOA of `V_L`.  (Classically
this is the rank-`L` Heisenberg VOA; no isomorphism with `HeisenbergN` is proved here.)  Restricting the adjoint module along it makes `V_L` a module over it,
**with the module Jacobi identity inherited from the proved VOA Jacobi identity**.  The
charge-`α` sectors of that module are the charged Fock modules `F_α`. -/

/-- **The charge-zero sub-VOA of `V_L`** (carrier `chargeSec L 0`).  Classically the Heisenberg
subalgebra; no isomorphism with a Heisenberg VOA is proved in Lean. -/
noncomputable def chargeZeroSubVOA (hEven : L.Even) (hPos : L.PosDef) :
    VOASubalgebra (latticeVOAGen L hEven hPos) where
  carrier := chargeSec L 0
  vacuum_mem := latVacuumGen_mem_chargeSec L
  conformal_mem := omegaLatGen_mem_chargeSec L
  smul_mem := fun _ hu n _ hv => chargeSec_zero_smul_mem L hEven hPos hu n hv
  graded := fun n _ hv => chargeSec_zero_graded L hEven hPos n hv

/-- **`V_L` is a module over its charge-zero sub-VOA** `chargeZeroSubVOA`.  The first genuinely non-adjoint
module in the library: obtained by restriction, so its module Jacobi identity is the *proved*
VOA Jacobi identity of `V_L`, not a fresh verification. -/
noncomputable def latticeAsHeisenbergModule (hEven : L.Even) (hPos : L.PosDef) :
    WeakModule (chargeZeroSubVOA L hEven hPos).toVOA (LatModuleGen L) :=
  (chargeZeroSubVOA L hEven hPos).adjointRestrict

/-- The charge-`α` sector is preserved by the Heisenberg action: it is a submodule of
`latticeAsHeisenbergModule`.  **This is `F_α`** — the charged Fock module, realized inside `V_L`
rather than constructed. -/
theorem chargeSec_invariant (hEven : L.Even) (hPos : L.PosDef) (α : L.carrier)
    (u : (chargeZeroSubVOA L hEven hPos).carrier) (n : ℤ)
    {x : LatModuleGen L} (hx : x ∈ chargeSec L α) :
    (latticeAsHeisenbergModule L hEven hPos).act u n x ∈ chargeSec L α := by
  have h := YfullGen_shiftsCharge L hEven hPos 0 u.2 α (-n - 1) x hx
  rwa [zero_add] at h

end VOA.LatGen
