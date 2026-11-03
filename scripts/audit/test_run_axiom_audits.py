import subprocess
import unittest
from unittest.mock import patch

from scripts.audit.run_axiom_audits import (
    BASE_AXIOMS,
    PBW_DECLARATION,
    PROBES,
    AxiomOutputError,
    Probe,
    execute_probe,
    parse_axiom_reports,
    validate_reports,
)


class AxiomOutputParserTests(unittest.TestCase):
    def test_parses_dependency_lines_and_ignores_warnings(self) -> None:
        output = """warning: harmless linter output
'VOA.clean' depends on axioms: [propext, Classical.choice, Quot.sound]
another benign line
'VOA.zhuModularity_pinned_of_C2Cofinite_voaPBW' depends on axioms: [propext,
 Classical.choice,
 VOA.pbw,
 Quot.sound]
"""
        reports = parse_axiom_reports(output)
        self.assertEqual(
            [(report.declaration, report.axioms) for report in reports],
            [
                (
                    "VOA.clean",
                    ("propext", "Classical.choice", "Quot.sound"),
                ),
                (
                    PBW_DECLARATION,
                    (
                        "propext",
                        "Classical.choice",
                        "VOA.pbw",
                        "Quot.sound",
                    ),
                ),
            ],
        )

    def test_axiom_free_reports_are_parsed_and_enforced(self) -> None:
        name = "VOA.AffineSl3.wordDegA_nil"
        output = f"'{name}' does not depend on any axioms\n"
        reports = parse_axiom_reports(output)
        self.assertEqual([(r.declaration, r.axioms) for r in reports], [(name, ())])
        self.assertEqual(validate_reports(Probe("test", "Test.lean", (name,)), reports), [])
        errors = validate_reports(Probe("test", "Test.lean", (name,)), reports + reports)
        self.assertTrue(any("appeared 2 times" in e for e in errors))
        # Empty reports are not a blanket exemption from exact dependency checks.
        unknown = parse_axiom_reports("'VOA.other' does not depend on any axioms")
        errors = validate_reports(Probe("test", "Test.lean", ("VOA.other",)), unknown)
        self.assertTrue(any("expected" in e for e in errors))

    def test_pbw_declaration_requires_base_axioms_only(self) -> None:
        # `VOA.pbw` is a theorem: a report still containing it must be rejected.
        probe = Probe("test", "Test.lean", ("VOA.clean", PBW_DECLARATION))
        clean = (
            "'VOA.clean' depends on axioms: "
            "[Quot.sound, propext, Classical.choice]\n"
            f"'{PBW_DECLARATION}' depends on axioms: "
            "[propext, Classical.choice, Quot.sound]\n"
        )
        self.assertEqual(validate_reports(probe, parse_axiom_reports(clean)), [])
        stale = (
            "'VOA.clean' depends on axioms: "
            "[Quot.sound, propext, Classical.choice]\n"
            f"'{PBW_DECLARATION}' depends on axioms: "
            "[propext, Classical.choice, VOA.pbw, Quot.sound]\n"
        )
        self.assertTrue(validate_reports(probe, parse_axiom_reports(stale)))

    def test_rejects_missing_duplicate_and_unexpected_declarations(self) -> None:
        probe = Probe("test", "Test.lean", ("VOA.one", "VOA.two"))
        base = ", ".join(BASE_AXIOMS)
        output = (
            f"'VOA.one' depends on axioms: [{base}]\n"
            f"'VOA.one' depends on axioms: [{base}]\n"
            f"'VOA.extra' depends on axioms: [{base}]\n"
        )
        errors = validate_reports(probe, parse_axiom_reports(output))
        self.assertTrue(any("appeared 2 times" in error for error in errors))
        self.assertTrue(any("missing dependency report" in error for error in errors))
        self.assertTrue(any("unexpected dependency report" in error for error in errors))

    def test_rejects_wrong_or_duplicate_axioms(self) -> None:
        probe = Probe("test", "Test.lean", ("VOA.bad", "VOA.dup"))
        output = """'VOA.bad' depends on axioms: [propext, Classical.choice, sorryAx, Quot.sound]
'VOA.dup' depends on axioms: [propext, propext, Classical.choice, Quot.sound]
"""
        errors = validate_reports(probe, parse_axiom_reports(output))
        self.assertTrue(any("sorryAx" in error for error in errors))
        self.assertTrue(any("duplicate axiom" in error for error in errors))

    def test_rejects_an_unclosed_dependency_report(self) -> None:
        with self.assertRaisesRegex(AxiomOutputError, "unclosed axiom list"):
            parse_axiom_reports(
                "warning: ignored\n"
                "'VOA.bad' depends on axioms: [propext,\n"
                " Classical.choice\n"
            )

    def test_nonzero_lean_exit_is_an_error(self) -> None:
        probe = Probe("test", "Test.lean", ())
        completed = subprocess.CompletedProcess(
            probe.command,
            returncode=7,
            stdout="",
            stderr="Lean failed",
        )
        with patch("scripts.audit.run_axiom_audits.subprocess.run", return_value=completed):
            errors, report_count = execute_probe(probe)
        self.assertEqual(report_count, 0)
        self.assertTrue(any("status 7" in error for error in errors))

    def test_maintained_probe_manifest_and_dj_option(self) -> None:
        by_name = {probe.name: probe for probe in PROBES}
        # Every probe that has ever been registered must still be here.  Additions by a
        # concurrent workflow are fine; silent deletions are not.
        self.assertLessEqual(
            {
                "GNHighHead",
                "GNLink2",
                "GNProp8",
                "Phase5",
                "DJCarrierWeak",
                "Super",
                "BlockFiniteEtingof",
                "AKZhuModularity",
                "Sl2Presentation",
                "GradedUnitarity",
                "GradedUnitarityLengthTwo",
                "NonlinearVirasoro",
                "NonlinearPresentation",
                "PairClosure",
            },
            set(by_name),
        )
        # Pin the exact size of the probe this workflow owns.  Do NOT reinstate a
        # hard-coded vector of every probe's size: several probes are maintained by
        # concurrent workflows, and one added declaration on their side broke this test
        # in a way that looked like it belonged to whoever ran it last.
        self.assertEqual(len(by_name["NonlinearPresentation"].declarations), 58)
        # Structural invariants every probe must satisfy, whoever owns it.
        self.assertEqual(len(PROBES), len(by_name))
        for probe in PROBES:
            self.assertGreater(len(probe.declarations), 0, probe.name)
            self.assertEqual(
                len(probe.declarations), len(set(probe.declarations)), probe.name
            )
        self.assertEqual(
            by_name["Sl2Presentation"].lean_options, ("-DmaxSynthPendingDepth=3",)
        )
        self.assertEqual(by_name["GradedUnitarity"].lean_options, ())


if __name__ == "__main__":
    unittest.main()
