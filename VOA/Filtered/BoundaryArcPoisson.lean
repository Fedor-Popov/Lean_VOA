import VOA.Filtered.AffineSl2UniversalJetPVA
import VOA.Commutative.InfiniteJetPVAHamiltonian
import VOA.Commutative.PoissonVertexQuotient
import VOA.Commutative.InfiniteJetPoissonUniqueness

/-!
# The intrinsic boundary arc Poisson vertex algebra

An unconditional universal affine PBW construction supplies the polynomial PVA.
Its generator modes are identified with the directly defined sl2 Hamiltonian
prolongations. The actual boundary ideal is then proved stable and every PVA
axiom descends to its genuine Hasse--Schmidt arc quotient.
-/
namespace VOA.BoundaryAuxiliary
open VOA.AffineSl2GeneralRigidity
noncomputable section

/-- The free sl2 jet PVA, using a fixed unconditional universal model. -/
def polynomialPVA : PoissonVertexAlgebra (JetPoly ℂ) :=
  universalJetPVA 0 (by norm_num)

@[simp] theorem polynomialPVA_translation : polynomialPVA.translation =
    InfiniteJet.polynomialTranslation := rfl

theorem polynomialPVA_base_zero (i j : Fin 3) :
    polynomialPVA.mode 0 (MvPolynomial.X (i,0)) (MvPolynomial.X (j,0)) =
      InfiniteJet.relationCoefficient (currentHamiltonian i (MvPolynomial.X j)) 0 := by
  rw [currentHamiltonian_X]
  exact universalJetPVA_base_zero 0 (by norm_num) i j

theorem polynomialPVA_base_succ (i j : Fin 3) (n : ℕ) :
    polynomialPVA.mode (n+1) (MvPolynomial.X (i,0)) (MvPolynomial.X (j,0)) = 0 :=
  universalJetPVA_base_succ 0 (by norm_num) i j n

/-- The actual polynomial PVA generator modes equal the intrinsic Hamiltonians. -/
theorem polynomialPVA_base_mode (i : Fin 3) (n : ℕ) (f : JetPoly ℂ) :
    polynomialPVA.mode n (MvPolynomial.X (i,0)) f =
      InfiniteJet.polynomialProlongation (currentHamiltonian i) n f :=
  InfiniteJet.base_mode_eq_prolongation polynomialPVA rfl currentHamiltonian
    polynomialPVA_base_zero polynomialPVA_base_succ i n f

theorem polynomialPVA_mode_left (m n : ℕ) (f : JetPoly ℂ)
    (hf : f ∈ InfiniteJet.jetIdeal (baseIdeal m)) (g : JetPoly ℂ) :
    polynomialPVA.mode n f g ∈ InfiniteJet.jetIdeal (baseIdeal m) :=
  InfiniteJet.mode_jetIdeal_left polynomialPVA rfl currentHamiltonian
    polynomialPVA_base_zero polynomialPVA_base_succ (baseIdeal m)
    (fun i => currentHamiltonian_baseIdeal_stable m i) n hf g

theorem polynomialPVA_mode_right (m n : ℕ) (f g : JetPoly ℂ)
    (hg : g ∈ InfiniteJet.jetIdeal (baseIdeal m)) :
    polynomialPVA.mode n f g ∈ InfiniteJet.jetIdeal (baseIdeal m) :=
  InfiniteJet.mode_jetIdeal_right polynomialPVA rfl currentHamiltonian
    polynomialPVA_base_zero polynomialPVA_base_succ (baseIdeal m)
    (fun i => currentHamiltonian_baseIdeal_stable m i) n f hg

/-- The genuine intrinsic PVA of the boundary arc algebra, with no character assumptions. -/
def arcPVA (m : ℕ) : PoissonVertexAlgebra (InfiniteJet.PresentedJet (baseIdeal (R := ℂ) m)) :=
  PoissonVertexAlgebra.quotient polynomialPVA (InfiniteJet.jetIdeal (baseIdeal m))
    (fun f hf => InfiniteJet.polynomialTranslation_stable (baseIdeal m) f hf)
    (polynomialPVA_mode_left m) (polynomialPVA_mode_right m)

/-- The descended translation is the original universal arc translation. -/
theorem arcPVA_translation (m : ℕ) :
    (arcPVA m).translation = InfiniteJet.translation (baseIdeal m) := by
  ext a
  obtain ⟨f,rfl⟩ := Ideal.Quotient.mk_surjective a
  rfl

/-- Every quotient mode evaluates by applying the actual polynomial PVA to representatives. -/
theorem arcPVA_mode_mk (m n : ℕ) (f g : JetPoly ℂ) :
    (arcPVA m).mode n (InfiniteJet.presentedJetMk (baseIdeal m) f)
      (InfiniteJet.presentedJetMk (baseIdeal m) g) =
      InfiniteJet.presentedJetMk (baseIdeal m) (polynomialPVA.mode n f g) := rfl

/-- The quotient generator modes are precisely the directly constructed arc Hamiltonians. -/
theorem arcPVA_generator_mode (m : ℕ) (i : Fin 3) (n : ℕ)
    (a : InfiniteJet.PresentedJet (baseIdeal (R := ℂ) m)) :
    (arcPVA m).mode n (InfiniteJet.generator (baseIdeal m) i 0) a =
      arcCurrentHamiltonian (R := ℂ) m i n a := by
  obtain ⟨f,rfl⟩ := Ideal.Quotient.mk_surjective a
  change (arcPVA m).mode n
    (InfiniteJet.presentedJetMk (baseIdeal m) (MvPolynomial.X (i,0)))
    (InfiniteJet.presentedJetMk (baseIdeal m) f) =
    InfiniteJet.prolongation (currentHamiltonian (R := ℂ) i) (baseIdeal m)
      (currentHamiltonian_baseIdeal_stable m i) n (InfiniteJet.presentedJetMk (baseIdeal m) f)
  rw [arcPVA_mode_mk,InfiniteJet.prolongation_mk,polynomialPVA_base_mode]

/-- Zeroth Hasse--Schmidt coefficient equals polynomial evaluation on zeroth jets. -/
theorem relationCoefficient_zero (f : BasePoly ℂ) :
    InfiniteJet.relationCoefficient f 0 = MvPolynomial.aeval
      (fun i : Fin 3 => MvPolynomial.X (i,0) : Fin 3 → JetPoly ℂ) f := by
  induction f using MvPolynomial.induction_on with
  | C c => simp [InfiniteJet.relationCoefficient,PowerSeries.algebraMap_apply]
  | add f g hf hg => simpa [InfiniteJet.relationCoefficient] using congrArg₂ (·+·) hf hg
  | mul_X f i hf =>
      simpa [InfiniteJet.relationCoefficient,InfiniteJet.generatorSeries] using
        congrArg (· * MvPolynomial.X (i,0)) hf

/-- The original generators retain the intrinsic sl2 Poisson bracket after quotienting. -/
theorem arcPVA_base_zero (m : ℕ) (i j : Fin 3) :
    (arcPVA m).mode 0 (InfiniteJet.generator (baseIdeal m) i 0)
      (InfiniteJet.generator (baseIdeal m) j 0) =
      MvPolynomial.aeval (fun a => InfiniteJet.generator (baseIdeal m) a 0)
        (currentPoissonBracket (R := ℂ) i j) := by
  change (arcPVA m).mode 0 (InfiniteJet.presentedJetMk (baseIdeal m) _)
    (InfiniteJet.presentedJetMk (baseIdeal m) _) = _
  rw [arcPVA_mode_mk,polynomialPVA_base_zero,currentHamiltonian_X,relationCoefficient_zero]
  have h : (InfiniteJet.presentedJetMk (baseIdeal (R := ℂ) m)).comp
      (MvPolynomial.aeval (fun a : Fin 3 => MvPolynomial.X (a,0))) =
      MvPolynomial.aeval (fun a => InfiniteJet.generator (baseIdeal m) a 0) := by
    apply MvPolynomial.algHom_ext
    intro a
    simp [InfiniteJet.generator]
  exact DFunLike.congr_fun h _

theorem arcPVA_base_succ (m : ℕ) (i j : Fin 3) (n : ℕ) :
    (arcPVA m).mode (n+1) (InfiniteJet.generator (baseIdeal m) i 0)
      (InfiniteJet.generator (baseIdeal m) j 0) = 0 := by
  change (arcPVA m).mode (n+1) (InfiniteJet.presentedJetMk (baseIdeal m) _)
    (InfiniteJet.presentedJetMk (baseIdeal m) _) = _
  rw [arcPVA_mode_mk,polynomialPVA_base_succ,map_zero]

/-- The intrinsic boundary arc PVA is uniquely characterized by translation and its base bracket.
In particular the construction does not depend on the auxiliary universal model. -/
theorem arcPVA_unique (m : ℕ)
    (P : PoissonVertexAlgebra (InfiniteJet.PresentedJet (baseIdeal (R := ℂ) m)))
    (hT : P.translation = InfiniteJet.translation (baseIdeal m))
    (hzero : ∀ i j, P.mode 0 (InfiniteJet.generator (baseIdeal m) i 0)
      (InfiniteJet.generator (baseIdeal m) j 0) =
      MvPolynomial.aeval (fun a => InfiniteJet.generator (baseIdeal m) a 0)
        (currentPoissonBracket (R := ℂ) i j))
    (hpos : ∀ i j n, P.mode (n+1) (InfiniteJet.generator (baseIdeal m) i 0)
      (InfiniteJet.generator (baseIdeal m) j 0) = 0) : P = arcPVA m := by
  apply InfiniteJet.poissonVertexAlgebra_unique (baseIdeal m) P (arcPVA m) hT
    (arcPVA_translation m)
  intro i j n
  cases n with
  | zero => rw [hzero,arcPVA_base_zero]
  | succ n => rw [hpos,arcPVA_base_succ]

end
end VOA.BoundaryAuxiliary
