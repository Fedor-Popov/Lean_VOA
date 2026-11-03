/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fedor K. Popov
-/
import VOA.Examples.LatticeGenVirasoroCharge

/-!
# Lattice word fields, Dong cascade, and reconstruction (general even positive-definite `L`)

The generating-field family `YwordLatGen l α` (iterated normal-ordered boson product `genFieldLatGen`
seeded by the charge field `Yeαvec α`), its `IsField`/`TrecGen`-covariance/creation-tower/span, the
Dong-cascade mutual locality (unconditional — both inputs `Yeαvec_local` and
`genFieldLatGen_local_Yeαvec` are proven), and the `Reconstruction.reconstruct` call yielding the
all-states vertex map `latYfullGen`.  Cross-charge lift of A₁'s `LatticeWordFields`/`LatticeReconstruct`.

All `sorry`-free, axiom-clean, `pbw`-free.
-/

set_option linter.style.longLine false

namespace VOA.LatGen

open scoped BigOperators TensorProduct
open Module (End)
open VOA VOA.IntegralLattice HeisenbergN Reconstruction

variable (L : IntegralLattice)

/-! ## §A  The word fields `YwordLatGen`. -/

/-- The iterated normal-ordered boson product seeded by the charge field `Yeαvec α`, with its field
witness.  `[] ↦ Yeαvec α`; `(i,a) :: rest ↦ :(genFieldLatGen a i)(YwordLatGen rest):`. -/
noncomputable def YwordLatGenF (α : L.carrier) :
    List (ℕ × Fin (rank L)) → { f : FormalDist (End ℂ (LatModuleGen L)) // IsField f }
  | [] => ⟨Yeαvec L α, Yeαvec_isField L α⟩
  | (ia :: rest) =>
      let p := YwordLatGenF α rest
      ⟨nprod (genFieldLatGen_isField L ia.2 ia.1) p.2,
        (genFieldLatGen_isField L ia.2 ia.1).nprod p.2⟩

/-- The lattice word field `YwordLatGen l α`. -/
noncomputable def YwordLatGen (l : List (ℕ × Fin (rank L))) (α : L.carrier) :
    FormalDist (End ℂ (LatModuleGen L)) := (YwordLatGenF L α l).1

theorem YwordLatGen_isField (l : List (ℕ × Fin (rank L))) (α : L.carrier) :
    IsField (YwordLatGen L l α) := (YwordLatGenF L α l).2

@[simp] theorem YwordLatGen_nil (α : L.carrier) : YwordLatGen L [] α = Yeαvec L α := rfl

theorem YwordLatGen_cons (ia : ℕ × Fin (rank L)) (rest : List (ℕ × Fin (rank L))) (α : L.carrier) :
    YwordLatGen L (ia :: rest) α
      = nprod (genFieldLatGen_isField L ia.2 ia.1) (YwordLatGen_isField L rest α) := rfl

/-! ## §B  `TrecGen`-covariance of the word fields. -/

theorem YwordLatGen_DCovariant (hPos : L.PosDef) :
    ∀ (l : List (ℕ × Fin (rank L))) (α : L.carrier),
      Reconstruction.DCovariant (TrecGen L) (YwordLatGen L l α)
  | [], α => by rw [YwordLatGen_nil]; exact TrecGen_Yeαvec_DCovariant L hPos α
  | (ia :: rest), α => by
      rw [YwordLatGen_cons]
      exact Reconstruction.DCovariant.nprod (genFieldLatGen_isField L ia.2 ia.1)
        (YwordLatGen_isField L rest α) (TrecGen_genFieldLatGen_DCovariant L ia.2 ia.1)
        (YwordLatGen_DCovariant hPos rest α)

/-! ## §C  The creation tower. -/

/-- The word-state map: the boson creation word applied to the charged vacuum `e^α`. -/
noncomputable def wordStateLatGen : List (ℕ × Fin (rank L)) → L.carrier → LatModuleGen L
  | [], α => latChargeGen L α
  | (ia :: rest), α =>
      LinearMap.rTensor (L.carrier →₀ ℂ) (currentN (rank L) 1 ia.2 ia.1) (wordStateLatGen rest α)

@[simp] theorem wordStateLatGen_nil (α : L.carrier) : wordStateLatGen L [] α = latChargeGen L α := rfl

theorem wordStateLatGen_cons (ia : ℕ × Fin (rank L)) (rest : List (ℕ × Fin (rank L))) (α : L.carrier) :
    wordStateLatGen L (ia :: rest) α
      = LinearMap.rTensor (L.carrier →₀ ℂ) (currentN (rank L) 1 ia.2 ia.1)
          (wordStateLatGen L rest α) := rfl

/-- **Creation tower (power-series part)**: `(YwordLatGen l α)_q |0⟩ = 0` for `q < 0`. -/
theorem YwordLatGen_vacuum_neg :
    ∀ (l : List (ℕ × Fin (rank L))) (α : L.carrier) {q : ℤ}, q < 0 →
      (YwordLatGen L l α) q (latVacuumGen L) = 0
  | [], α, q, hq => by rw [YwordLatGen_nil, Yeαvec_vacuum, if_neg (by omega)]
  | (ia :: rest), α, q, hq => by
      rw [YwordLatGen_cons]
      exact nprod_vacuum_neg_gen (genFieldLatGen_isField L ia.2 ia.1) (YwordLatGen_isField L rest α)
        (latVacuumGen L) (fun s hs => genFieldLatGen_vacuum_neg L ia.2 ia.1 hs)
        (fun s hs => YwordLatGen_vacuum_neg rest α hs) hq

/-- **Creation tower (base)**: `(YwordLatGen l α)_0 |0⟩ = wordStateLatGen l α`. -/
theorem YwordLatGen_vacuum_base :
    ∀ (l : List (ℕ × Fin (rank L))) (α : L.carrier),
      (YwordLatGen L l α) 0 (latVacuumGen L) = wordStateLatGen L l α
  | [], α => by rw [YwordLatGen_nil, wordStateLatGen_nil, Yeαvec_creation_z0]
  | (ia :: rest), α => by
      rw [YwordLatGen_cons,
        nprod_vacuum_base_gen (genFieldLatGen_isField L ia.2 ia.1) (YwordLatGen_isField L rest α)
          (latVacuumGen L) (fun s hs => genFieldLatGen_vacuum_neg L ia.2 ia.1 hs)
          (fun s hs => YwordLatGen_vacuum_neg L rest α hs),
        genFieldLatGen_zero_op, YwordLatGen_vacuum_base rest α, wordStateLatGen_cons]

/-! ## §D  Spanning of the word states. -/

/-- The word state is the boson monomial (`wordStateN`) tensored with the lattice point `e^α`. -/
theorem wordStateLatGen_eq (l : List (ℕ × Fin (rank L))) (α : L.carrier) :
    wordStateLatGen L l α = (wordStateN l) ⊗ₜ[ℂ] eGen L α := by
  induction l with
  | nil => rw [wordStateLatGen_nil, wordStateN_nil, latChargeGen, latStateGen, vacuumN]
  | cons ia rest ih =>
      rw [wordStateLatGen_cons, ih, wordStateN_cons, LinearMap.rTensor_tmul]
      congr 1
      rw [currentN_apply, oscN_neg (rank L) 1 ia.2 (show -((ia.1 : ℤ)) - 1 < 0 by omega),
        show (-(-((ia.1 : ℤ)) - 1) - 1).toNat = ia.1 from by omega, mulXN_apply]

/-- **The word states span** `V_L`. -/
theorem wordStateLatGen_span :
    Submodule.span ℂ (Set.range (Function.uncurry (wordStateLatGen L))) = ⊤ := by
  set S := Submodule.span ℂ (Set.range (Function.uncurry (wordStateLatGen L))) with hS
  have hmono : ∀ (a : (ℕ × Fin (rank L)) →₀ ℕ) (α : L.carrier),
      (MvPolynomial.monomial a (1 : ℂ)) ⊗ₜ[ℂ] eGen L α ∈ S := by
    intro a α
    have hword : wordStateLatGen L (HeisenbergN.monoWordN a) α
        = (MvPolynomial.monomial a (1 : ℂ)) ⊗ₜ[ℂ] eGen L α := by
      rw [wordStateLatGen_eq, HeisenbergN.wordStateN_monoWordN]
    rw [← hword]
    exact Submodule.subset_span ⟨(HeisenbergN.monoWordN a, α), rfl⟩
  have hpe : ∀ (p : FockN (rank L)) (α : L.carrier), p ⊗ₜ[ℂ] eGen L α ∈ S := by
    intro p α
    rw [← MvPolynomial.support_sum_monomial_coeff p, TensorProduct.sum_tmul]
    refine Submodule.sum_mem _ (fun a _ => ?_)
    rw [show (MvPolynomial.monomial a (MvPolynomial.coeff a p))
          = (MvPolynomial.coeff a p) • MvPolynomial.monomial a (1 : ℂ) from by
        rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one],
      ← TensorProduct.smul_tmul' (MvPolynomial.coeff a p) (MvPolynomial.monomial a (1 : ℂ))
        (eGen L α)]
    exact Submodule.smul_mem _ _ (hmono a α)
  rw [hS, eq_top_iff, ← TensorProduct.span_tmul_eq_top ℂ (FockN (rank L)) (L.carrier →₀ ℂ),
    Submodule.span_le]
  rintro _ ⟨p, g, rfl⟩
  rw [SetLike.mem_coe]
  induction g using Finsupp.induction_linear with
  | zero => erw [TensorProduct.tmul_zero]; exact Submodule.zero_mem _
  | add g1 g2 h1 h2 =>
      erw [TensorProduct.tmul_add]; exact Submodule.add_mem _ h1 h2
  | single α c =>
      rw [show (Finsupp.single α c : L.carrier →₀ ℂ) = c • eGen L α from by
          rw [eGen, Finsupp.smul_single, smul_eq_mul, mul_one]]
      erw [TensorProduct.tmul_smul]
      exact Submodule.smul_mem _ _ (hpe p α)

/-! ## §E  The Dong locality cascade (unconditional). -/

/-- The boson generator field is local with every word field (Dong cascade over the boson word). -/
theorem genFieldLatGen_local_YwordLatGen (hEven : L.Even) (hPos : L.PosDef) (a : Fin (rank L)) (i : ℕ) :
    ∀ (l : List (ℕ × Fin (rank L))) (α : L.carrier),
      Local (genFieldLatGen L a i) (YwordLatGen L l α)
  | [], α => by rw [YwordLatGen_nil]; exact genFieldLatGen_local_Yeαvec L a i α
  | (jb :: rest), α => by
      rw [YwordLatGen_cons]
      have hab : Local (genFieldLatGen L jb.2 jb.1) (YwordLatGen L rest α) :=
        genFieldLatGen_local_YwordLatGen hEven hPos jb.2 jb.1 rest α
      have hac : Local (genFieldLatGen L jb.2 jb.1) (genFieldLatGen L a i) :=
        genFieldLatGen_local L jb.2 a jb.1 i
      have hbc : Local (YwordLatGen L rest α) (genFieldLatGen L a i) :=
        (genFieldLatGen_local_YwordLatGen hEven hPos a i rest α).symm
      exact (dong_neg (genFieldLatGen_isField L jb.2 jb.1) (YwordLatGen_isField L rest α)
        hab hac hbc).symm

/-- The charge seed `Yeαvec α` is local with every word field, using the proven `Yeαvec_local`. -/
theorem Yeαvec_local_YwordLatGen (hEven : L.Even) (hPos : L.PosDef) (α : L.carrier) :
    ∀ (l : List (ℕ × Fin (rank L))) (β : L.carrier),
      Local (Yeαvec L α) (YwordLatGen L l β)
  | [], β => by rw [YwordLatGen_nil]; exact Yeαvec_local L hEven hPos α β
  | (jb :: rest), β => by
      rw [YwordLatGen_cons]
      have hab : Local (genFieldLatGen L jb.2 jb.1) (YwordLatGen L rest β) :=
        genFieldLatGen_local_YwordLatGen L hEven hPos jb.2 jb.1 rest β
      have hac : Local (genFieldLatGen L jb.2 jb.1) (Yeαvec L α) :=
        genFieldLatGen_local_Yeαvec L jb.2 jb.1 α
      have hbc : Local (YwordLatGen L rest β) (Yeαvec L α) :=
        (Yeαvec_local_YwordLatGen hEven hPos α rest β).symm
      exact (dong_neg (genFieldLatGen_isField L jb.2 jb.1) (YwordLatGen_isField L rest β)
        hab hac hbc).symm

/-- **Every two word fields are mutually local** (unconditional). -/
theorem YwordLatGen_local (hEven : L.Even) (hPos : L.PosDef) :
    ∀ (l₁ : List (ℕ × Fin (rank L))) (α₁ : L.carrier) (l₂ : List (ℕ × Fin (rank L))) (α₂ : L.carrier),
      Local (YwordLatGen L l₁ α₁) (YwordLatGen L l₂ α₂)
  | [], α₁, l₂, α₂ => by rw [YwordLatGen_nil]; exact Yeαvec_local_YwordLatGen L hEven hPos α₁ l₂ α₂
  | (ia :: rest), α₁, l₂, α₂ => by
      rw [YwordLatGen_cons]
      have hab : Local (genFieldLatGen L ia.2 ia.1) (YwordLatGen L rest α₁) :=
        genFieldLatGen_local_YwordLatGen L hEven hPos ia.2 ia.1 rest α₁
      have hac : Local (genFieldLatGen L ia.2 ia.1) (YwordLatGen L l₂ α₂) :=
        genFieldLatGen_local_YwordLatGen L hEven hPos ia.2 ia.1 l₂ α₂
      have hbc : Local (YwordLatGen L rest α₁) (YwordLatGen L l₂ α₂) :=
        YwordLatGen_local hEven hPos rest α₁ l₂ α₂
      exact dong_neg (genFieldLatGen_isField L ia.2 ia.1) (YwordLatGen_isField L rest α₁) hab hac hbc

/-! ## §F  The reconstructed all-states vertex map. -/

/-- **The basis-free lattice vertex map** from the reconstruction engine (unconditional): `YfullGen`
with word evaluation, `IsField`, mutual locality, the VA3 creation tower, and `TrecGen`-covariance. -/
theorem latYfullGen_of_locality (hEven : L.Even) (hPos : L.PosDef) :
    ∃ Yfull : LatModuleGen L →ₗ[ℂ] FormalDist (End ℂ (LatModuleGen L)),
      (∀ (lα : List (ℕ × Fin (rank L)) × L.carrier),
        Yfull (Function.uncurry (wordStateLatGen L) lα)
          = Function.uncurry (fun l α => YwordLatGen L l α) lα) ∧
      (∀ u : LatModuleGen L, IsField (Yfull u)) ∧
      (∀ u v : LatModuleGen L, Local (Yfull u) (Yfull v)) ∧
      (∀ u : LatModuleGen L, (Yfull u) 0 (latVacuumGen L) = u) ∧
      (∀ u : LatModuleGen L, ∀ q : ℤ, q < 0 → (Yfull u) q (latVacuumGen L) = 0) ∧
      (∀ u : LatModuleGen L, Reconstruction.DCovariant (TrecGen L) (Yfull u)) :=
  Reconstruction.reconstruct (latVacuumGen L) (Function.uncurry (wordStateLatGen L))
    (Function.uncurry (fun l α => YwordLatGen L l α)) (TrecGen L)
    (wordStateLatGen_span L)
    (fun lα => YwordLatGen_isField L lα.1 lα.2)
    (fun lα₁ lα₂ => YwordLatGen_local L hEven hPos lα₁.1 lα₁.2 lα₂.1 lα₂.2)
    (fun lα => YwordLatGen_vacuum_base L lα.1 lα.2)
    (fun lα _q hq => YwordLatGen_vacuum_neg L lα.1 lα.2 hq)
    (TrecGen_vacuum L)
    (fun lα => YwordLatGen_DCovariant L hPos lα.1 lα.2)

end VOA.LatGen
