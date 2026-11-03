import VOA.DeligneAudit.D4CoreSingleAdjointBoundAudit
import VOA.DeligneAudit.D4CoreCapstoneAudit
import VOA.DeligneAudit.D4LevelReductionTwoAdjointCapstone
import VOA.DeligneAudit.D4LevelReductionSplitAdjointWeylBound

/-!
The D4 capstone with the single-adjoint core family discharged, and the split-adjoint Weyl bound.

The remaining hypothesis is exactly the core rank bound with at least two adjoint sites
and a positive central count. The conclusion retains both classical freeness and the
presentation-kernel equality from the capstone.

The independent sl4 result is `truncatedWeyl_sl4_splitAdjoint_rank_le`:
the universal module `SL4T.TruncatedLabelModule a b a (a + b + j)` is finite-dimensional
and has dimension at most `16 ^ j * 15 ^ (a - j) * 6 ^ b` whenever `j ≤ a`.
All parameters are arbitrary natural numbers, including the zero-weight boundary.
The companion `truncatedWeyl_sl4_splitAdjoint_cyclic_bound` transfers the estimate
to every cyclic realization with the local Weyl relations and the stated current cutoff.

The proof uses the quotient by the cyclic span of the last retained highest-root mode.
The quotient generator has the previous current cutoff. The removed cyclic submodule
is a quotient of the truncated Weyl module with both outer labels reduced by one and
cutoff reduced by two. Its highest-weight relations follow from the non-highest-root
mode cutoffs. The quadratic Garland coefficient at the next-to-top degree gives the
remaining highest-root cutoff. Only this single cutoff mode is needed: the established
current-ideal argument then gives all higher modes. Rank-nullity gives
`sl4TruncatedLabel_rank_step`, and induction on the number of split adjoint sites
starts from `SL4T.mixedLabelTruncatedRank`.

Axiom check: no `sorryAx` occurs, and every theorem of this layer depends exactly on
`propext`, `Classical.choice` and `Quot.sound`. This audit imports both results together.

Both all-parameter results are proved. **Not proved here:** the remaining D4
mathematical obligation `TruncatedCoreRankBound a b c` for `2 ≤ a` and `1 ≤ c`.
The split-adjoint bound controls highest-weight truncated Weyl quotients; it does not
itself establish those remaining core bounds. No unresolved Lean obligation or
additional mathematical hypothesis is hidden in the split-adjoint theorem.
-/

#print axioms VOA.DeligneAudit.D4LevelReduction.d4_classicallyFree_of_twoAdjointCoreBounds
#print axioms VOA.DeligneAudit.D4LevelReduction.sl4TruncatedLabel_rank_step
#print axioms VOA.DeligneAudit.D4LevelReduction.truncatedWeyl_sl4_splitAdjoint_rank_le
#print axioms VOA.DeligneAudit.D4LevelReduction.truncatedWeyl_sl4_splitAdjoint_cyclic_bound
