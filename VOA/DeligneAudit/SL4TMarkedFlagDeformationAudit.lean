import VOA.DeligneAudit.SL4TMarkedFlagDescentAudit
import VOA.DeligneAudit.SL4TDoublyMarkedTwoMinorForm

/-!
# The marked full-flag stratum ideals in complement form: declaration and axiom audit

**Status.** Every stratum ideal used at one adjoint site is identified with the corresponding
top-row minor ideal, in complement form, for all parameters. Notation: a coinvariant alphabet
`x`, `Y` with complement `Z`, `r = |Y|`, `P_Y = ∏_Y (t - x)`.

* One-minor ideals (`SL4TMarkedFlagComplementForm`): `(∏ Z, s c(Z))` on the singly marked flag
  with one double, `(∏ Z, c(Z))` on the doubly marked flag.
* Two-minor ideal of the doubly marked flag (`SL4TDoublyMarkedTwoMinorForm`): for `r ≥ 2`,
  `Z ≠ ∅` and `n = h + 3`, the top-row two-minors of the columns `t^m`, `m ≥ h + 1`, are Hankel
  minors of the coefficients `H_k` of `∏_Z (1 - x t)` (`topRow_pair_entries`), and
  `G_2(t^(h+1)) = ((∏ Z)²)` (`topIdeal_two_power_eq_sq`); with `s = 0` the joint two-minor ideal
  is the same (`jointTopIdeal_two_eq_sq_of_zero`).

Together with `SL4TMarkedFlagStrataJointAudit`, the dimension of every joint top-row minor ideal
`G_j`, `j = 1, 2`, of the marked full flags with one double is bounded below by the number of
configurations with at least `j` T-points.

**Not proved here.** `OneAdjointStratumCount B 1` remains open; its first two conjuncts are open.
Open nodes:

* `G_j = 0` above the T-point count (`j ≥ 2` singly marked, `j ≥ 3` doubly marked), and the
  deformation lower bound `dim C/G_j ≥ #(configurations with fewer than j T-points)`, preferably
  as an equivariant identification of `C/G_j` with the graded configuration ring;
* the presentation of `AdjointSiteCoefficientRing (mixedLabelBlockParams 1 B d e₁ e₂) (B - 1)` as
  the colour invariants of the marked full flag, the descent of `G_j`, and the orbit count
  `adjointSiteWordCount`.

Axioms of every declaration are printed below.
-/

-- SL4TDoublyMarkedTwoMinorForm.lean
#print axioms VOA.DeligneAudit.SL4T.hankel_two_mem
#print axioms VOA.DeligneAudit.SL4T.hankel_two_top
#print axioms VOA.DeligneAudit.SL4T.topRow_pair_entries
#print axioms VOA.DeligneAudit.SL4T.topIdeal_two_power_eq_sq
#print axioms VOA.DeligneAudit.SL4T.jointTopIdeal_two_eq_sq_of_zero
