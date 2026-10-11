"""Install/build seven frozen platform modules without overwriting work."""
from __future__ import annotations
import hashlib
import json
from pathlib import Path, PurePosixPath
import subprocess
import sys
import argparse

TASK = Path(__file__).resolve().parents[1]
ROOT = TASK.parents[1]
OUT = TASK / "formalization/platform/coefficient-map"
AUTHOR = "f5d04a3297e7c28f233fec3b7db822c8b63570dab1b00c910b0c3286490fc1e6"
PLAN = "5dadb5ca13fdf18862387315abb9da410fae4a81a5290e875ed972233ef28e8b"
SOURCE = "e055780f1abf389593fbccba2194fc52ee85108bbb4593439c32230944b3ab03"


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load(path):
    return json.loads(path.read_text(encoding="utf-8"))


def main():
    global OUT, AUTHOR, PLAN, SOURCE
    sys.stdout.reconfigure(encoding="utf-8")
    parser = argparse.ArgumentParser()
    parser.add_argument("batch", nargs="?", choices=("coefficient-map", "coefficient-map-jet", "coefficient-map-injectivity", "coefficient-map-partial-fractions", "coefficient-map-reflection", "coefficient-map-finite-sum", "coefficient-map-summation", "coefficient-map-shift-degree", "coefficient-map-aggregate", "coefficient-map-telescoper", "coefficient-map-kernel-bridge", "coefficient-map-connection", "coefficient-map-matrix"), default="coefficient-map")
    args = parser.parse_args()
    checks = 11
    stem = "ZetaNine_CoefficientMap"
    if args.batch == "coefficient-map-jet":
        OUT = TASK / "formalization/platform/coefficient-map-jet"
        AUTHOR = "a2b03ceb4e2ac3d2c4bc062f32cd8dcbac73b68bc0799802e886365eed6f3345"
        PLAN = "69972187996b6f673479bdfb3fa4cbefa831cd6b50bbdce1d54665b07d9d812a"
        SOURCE = "e50e11c0afd2eaac1d5c58c412e5e59bc5c2068c9826063eacee8dc88fc1735a"
        checks = 13
        stem = "ZetaNine_CoefficientMapJet"
    elif args.batch == "coefficient-map-injectivity":
        OUT = TASK / "formalization/platform/coefficient-map-injectivity"
        AUTHOR = "b91251de9261a7656de3274575072995452706d8a9ee0e570ae9ded4ce5b2253"
        PLAN = "51bc6ae331a1e8b781c4dd8250248e4bed8e7c5092bb50db5bcd73f4423cf9c3"
        SOURCE = "ebe9b9c275a34fac348837e377e2e26246e9a762889c462420b43535e9055095"
        checks = 16
        stem = "ZetaNine_CoefficientMapInjectivity"
    elif args.batch == "coefficient-map-partial-fractions":
        OUT = TASK / "formalization/platform/coefficient-map-partial-fractions"
        AUTHOR = "d416ad774d2f4a7b599151aef4f460a42395f116cf5e13d577d311ca2a9aa20f"
        PLAN = "6d60147f78b8463471c32fb257c9fd3fbad22c970733487c469dfb821650b847"
        SOURCE = "eb0b8d54cd29ddaaa9404ee26a704bb6a47e8306741c49a6bba9b7232231f61a"
        checks = 22
        stem = "ZetaNine_CoefficientMapPartialFractions"
    elif args.batch == "coefficient-map-reflection":
        OUT = TASK / "formalization/platform/coefficient-map-reflection"
        AUTHOR = "7d48c5b7197fc9d9543b35063c256aa73bea606a59866ea81df227f731105651"
        PLAN = "d8a5022833267eba1884f519a2f61b80343dfae4f53820e80ae57c2c9a6e5ad6"
        SOURCE = "8fbc53b9d9c33a61e1cf8208f89cd30dd3c6793fc32aad1cad1c51286747f707"
        checks = 25
        stem = "ZetaNine_CoefficientMapReflection"
    elif args.batch == "coefficient-map-finite-sum":
        OUT = TASK / "formalization/platform/coefficient-map-finite-sum"
        AUTHOR = "b3b91da77d5c2523fdd9b091351ac302540206d4a882f24e8c0d6476e504eaf0"
        PLAN = "3e89c024cc54d362fcf6e2ef6b6ca90272ff675883266176f266d2bc6a231094"
        SOURCE = "b3ede123541d6c0eb306915d93f743979b1090c34bc4df332ab6e9da07033f97"
        checks = 29
        stem = "ZetaNine_CoefficientMapFiniteSum"
    elif args.batch == "coefficient-map-summation":
        OUT = TASK / "formalization/platform/coefficient-map-summation"
        AUTHOR = "eed4d2dc0cd429401cf7b7bbffd34cb556cc2159f773c57dcdb8fe9cbee37a79"
        PLAN = "ab40b8a9bbb5904e1d6c277c7408803eb60d9b64efd0fea0af14c607386d4adc"
        SOURCE = "c207e8fec1358e86afd61d39853a498c9758555286b7774e5f5d7809495e876d"
        checks = 25
        stem = "ZetaNine_CoefficientMapSummation"
    elif args.batch == "coefficient-map-shift-degree":
        OUT = TASK / "formalization/platform/coefficient-map-shift-degree"
        AUTHOR = "6139eee95fa63d6427a2bced0171b7ae9c5ec6917fcfa124802a995f32e06e18"
        PLAN = "48edfb368179cb7ed0f746ca2acc4bbafc06103d5e6bc498cdc8b4e6e42e3cb9"
        SOURCE = "96efe64f218c07a9d941136af1b4a0874bca9627c01be262c53e4445e0876953"
        checks = 24
        stem = "ZetaNine_CoefficientMapShiftDegree"
    elif args.batch == "coefficient-map-aggregate":
        OUT = TASK / "formalization/platform/coefficient-map-aggregate"
        AUTHOR = "f7062cfecbbe14e5d36e69165e159630f4e090bbe1989b5d79ddc9bae2435ddf"
        PLAN = "defc8a43e447894f4024a70abc7e551738f15e20dcad220870d0984d79b4366d"
        SOURCE = "e538a7310f81ce9ab6c5e07d4b8bd64bb70be7a899e28f085a2c8506a4ff2299"
        checks = 35
        stem = "ZetaNine_CoefficientMapAggregate"
    elif args.batch == "coefficient-map-telescoper":
        OUT = TASK / "formalization/platform/coefficient-map-telescoper"
        AUTHOR = "28f93d0ab2f580cf7edae113ce297e40486882de33236d0bac08d426ee2abe0b"
        PLAN = "7162be6b7d324c74cc961a35a29b2b7ef24111ee086dfb09243425d175bd46bb"
        SOURCE = "8792e8ba5c6abcbdbe83b0aa4ffa1ab716fd05fac10da7275b86ab2f780fd121"
        checks = 40
        stem = "ZetaNine_CoefficientMapTelescoper"
    elif args.batch == "coefficient-map-kernel-bridge":
        OUT = TASK / "formalization/platform/coefficient-map-kernel-bridge"
        AUTHOR = "d0c86d3cb8f08e6c9e961782718cbedb8c319f4805002586cfa286f68d7eb057"
        PLAN = "6767eca98651d8c1e5867134bb981b1ccf3a45ed24ea5603b067c71a113abf28"
        SOURCE = "1ec15a46ae656bb0be0de0eb44afeca3144a7223a84eecf161693be25205bedb"
        checks = 52
        stem = "ZetaNine_CoefficientMapKernelBridge"
    elif args.batch == "coefficient-map-connection":
        OUT = TASK / "formalization/platform/coefficient-map-connection"
        AUTHOR = "876033891293bc5fdf4f8846d26d099631a5124c6f6c245e5c1ad996bd8779e5"
        PLAN = "19dd8f1d73b41cb10c1d85c9822ad80deb5082c0c721158488684a48d1a18d66"
        SOURCE = "098d82f606b5b6fda1e1d08524ef23db3ed3943a90ae109439f5046c031337e8"
        checks = 33
        stem = "ZetaNine_CoefficientMapConnection"
    elif args.batch == "coefficient-map-matrix":
        OUT = TASK / "formalization/platform/coefficient-map-matrix"
        AUTHOR = "c908b981d4fbb5b9c84ec137e829e1a1ac06b382640ef447811208b23bc09f8e"
        PLAN = "94e573d015d6aba167adc32bad6e7b6427a81cfdf290e7483415ce2fbee7498c"
        SOURCE = "a4bf1766c8bbcc1f2f83af27594ba10b3dfcd4e55058f10ccc4d4b25cb9c6d99"
        checks = 33
        stem = "ZetaNine_CoefficientMapMatrix"
    assert digest(OUT / "author-audit.json") == AUTHOR
    assert digest(OUT / "root-copy-plan.json") == PLAN
    audit = load(OUT / "author-audit.json")
    assert audit["verdict"] == "PASS" and audit["source_sha256"] == SOURCE
    assert len(audit["checks"]) == checks and all(c["pass"] for c in audit["checks"])
    for row in audit["stable_files"]:
        path = TASK / row["task_relative"]
        assert path.resolve().is_relative_to(TASK.resolve())
        assert digest(path) == row["sha256"] and path.stat().st_size == row["bytes"], row["task_relative"]
    separate_native_reviews = {"coefficient-map-summation", "coefficient-map-shift-degree", "coefficient-map-aggregate", "coefficient-map-telescoper", "coefficient-map-kernel-bridge", "coefficient-map-connection", "coefficient-map-matrix"}
    native_date = "2026-10-04" if args.batch in separate_native_reviews else "2026-10-03"
    native_stem = args.batch + "-independent" if args.batch in separate_native_reviews else args.batch
    native_review_path = TASK / ("verification/formalization-" + native_stem + "-" + native_date + "/independent-review.json")
    native_review = load(native_review_path)
    if args.batch == "coefficient-map":
        assert native_review["status"] == "PASS"
        assert native_review["verdict"] == "PASS_ACTUAL_FINITE_LEADING_POLE_ENTRY_ONLY"
        assert native_review["source_sha256"] == SOURCE and len(native_review["checks"]) == 14
    elif args.batch == "coefficient-map-jet":
        assert native_review["status"] == "PASS"
        assert native_review["verdict"] == "PASS_ACTUAL_FORMAL_LOCAL_ALL_NINE_ORDERS_ONLY"
        assert native_review["sources_sha256"]["CoefficientMapJet.lean"] == SOURCE
        assert len(native_review["checks"]) == 16
    elif args.batch == "coefficient-map-injectivity":
        assert digest(TASK / "verification/formalization-coefficient-map-injectivity-2026-10-03/independent-review.json") == "a271a7c004845f9151f79c7779cea6c451337d65890922fd8a15dae9a5aea747"
        assert native_review["verdict"] == "PASS"
        assert native_review["scope_verdict"] == "PASS_ACTUAL_PROPER_COMPLETE_LOCAL_COEFFICIENT_ARRAY_INJECTIVITY_ONLY"
        assert native_review["source_sha256"] == SOURCE and len(native_review["checks"]) == 16
    elif args.batch == "coefficient-map-partial-fractions":
        assert digest(TASK / "verification/formalization-coefficient-map-partial-fractions-2026-10-03/independent-review.json") == "df4d12de4529335fca0070e5d71294f396d8a00ef3fc9045cc74188f187ecea9"
        assert native_review["verdict"] == "PASS"
        assert native_review["scope_verdict"] == "PASS_ACTUAL_FINITE_GLOBAL_PARTIAL_FRACTIONS_IN_PROPER_REGULAR_DOMAIN_ONLY"
        assert native_review["source_sha256"] == SOURCE and len(native_review["checks"]) == 16
    elif args.batch == "coefficient-map-reflection":
        assert digest(TASK / "verification/formalization-coefficient-map-reflection-2026-10-03/independent-review.json") == "ac3d8f135cb3c69b39074548bea712f418fa6d0273ad27e33805374c1db20123"
        assert native_review["verdict"] == "PASS"
        assert native_review["scope_verdict"] == "PASS_ACTUAL_P9_M_N_REFLECTION_AND_ORIGINAL_INTEGER_QUARTIC_CANCELLATIONS_ONLY"
        assert native_review["source_sha256"] == SOURCE and len(native_review["checks"]) == 17
    elif args.batch == "coefficient-map-finite-sum":
        assert digest(TASK / "verification/formalization-coefficient-map-finite-sum-2026-10-03/independent-review.json") == "a4d2cec35a3e9b506aed7a0df0b2afacce4adf07a5b03f42b713b9726b581386"
        assert native_review["verdict"] == "PASS"
        assert native_review["scope_verdict"] == "PASS_ACTUAL_FINITE_SUM_IN_PROPER_DOMAIN_AND_CONDITIONAL_CANCELLATION_BRIDGES_ONLY"
        assert native_review["source_sha256"] == SOURCE and len(native_review["checks"]) == 15
    elif args.batch == "coefficient-map-summation":
        assert digest(native_review_path) == "fb0d4a09e3273fe430688521771ea582463d31cd98caf50764a7498293c040fa"
        assert native_review["verdict"] == "PASS"
        assert native_review["scope_verdict"] == "PASS_ACTUAL_P9_Q1_M_N_D0_ABSOLUTE_SUMMABILITY_AND_EXACT_INFINITE_L_ONLY"
        assert native_review["source_sha256"] == SOURCE and len(native_review["checks"]) == 16
    elif args.batch == "coefficient-map-shift-degree":
        assert digest(native_review_path) == "d38de9f7991fedbd716bd2b1824cda09f979c1da91191bff43e8f0ea3922e5df"
        assert native_review["verdict"] == "PASS"
        assert native_review["scope_verdict"] == "PASS_ACTUAL_POLYNOMIAL_SHIFT_OPERATOR_COEFFICIENT_AND_DEGREE_OBSTRUCTION_ONLY"
        assert native_review["source_sha256"] == SOURCE and len(native_review["checks"]) == 16
    elif args.batch == "coefficient-map-telescoper":
        assert digest(native_review_path) == "cac46e0ea0674bcd4b2dca543326ab2d9bdd3cd8a409cba8988bfea0130a556a"
        assert native_review["verdict"] == "PASS"
        assert native_review["scope_verdict"] == "PASS_ACTUAL_CUMULATIVE_TELESCOPER_ROOT_DIVISIBILITY_AND_QUOTIENT_BOUND_ONLY"
        assert native_review["source_sha256"] == SOURCE and len(native_review["checks"]) == 16
    elif args.batch == "coefficient-map-kernel-bridge":
        assert digest(native_review_path) == "7a325b3866719750c31e66469399ab85f7c73d8c5c1376356ee1951b320d78b1"
        assert native_review["verdict"] == "PASS"
        assert native_review["scope_verdict"] == "PASS_ACTUAL_ORIGINAL_EVEN_N_AT_LEAST_TWO_QUARTIC_F_KERNEL_INVERSE_AND_PRESCRIBED_ABSOLUTE_HASSUM"
        assert native_review["source_sha256"] == SOURCE and len(native_review["checks"]) == 22
        assert len(native_review["stable_files"]) == 296
        for row in native_review["stable_files"]:
            assert digest(ROOT / row["root_relative"]) == row["sha256"]
    elif args.batch == "coefficient-map-connection":
        assert digest(native_review_path) == "92940f9b02161210e55af39c625e0cd233eaf7a5bf9d5c1aa2238f0506e28d82"
        assert native_review["verdict"] == "PASS" and native_review["source_sha256"] == SOURCE
        assert len(native_review["checks"]) == 28 and len(native_review["stable_files"]) == 108
        assert native_review["counts"]["source_definitions"] == 12
        assert native_review["counts"]["source_theorems"] == 27
        assert set(native_review["standard_axioms"]) == {"propext", "Classical.choice", "Quot.sound"}
        for row in native_review["stable_files"]:
            path = ROOT / row["root_relative"]
            assert path.resolve().is_relative_to(ROOT.resolve())
            if row.get("task_relative"):
                assert path.resolve() == (TASK / row["task_relative"]).resolve()
            assert path.stat().st_size == row["bytes"] and digest(path) == row["sha256"]
    elif args.batch == "coefficient-map-matrix":
        assert digest(native_review_path) == "c333e8459bd458d62b4a48917a188970c9579ecea6e9707998d9a0289ceb2e72"
        assert native_review["verdict"] == "PASS" and native_review["source_sha256"] == SOURCE
        assert len(native_review["checks"]) == 32 and len(native_review["stable_files"]) == 517
        for row in native_review["stable_files"]:
            path = ROOT / row["root_relative"]
            assert path.resolve().is_relative_to(ROOT.resolve())
            assert path.stat().st_size == row["bytes"] and digest(path) == row["sha256"]
    else:
        assert args.batch == "coefficient-map-aggregate"
        assert digest(native_review_path) == "d2f50aa65f5dec147e632642c78cd27aaa7d8b7ba554067b389d5cc669002ddc"
        assert native_review["verdict"] == "PASS"
        assert native_review["scope_verdict"] == "PASS_ACTUAL_F_LINEARITY_AND_QUARTIC_COORDINATES_ONLY"
        assert native_review["source_sha256"] == SOURCE and len(native_review["checks"]) == 15
    assert all(c["pass"] for c in native_review["checks"])
    plan = load(OUT / "root-copy-plan.json")
    if args.batch == "coefficient-map-injectivity":
        assert plan["sources_sha256"]["CoefficientMapInjectivity"] == SOURCE
    else:
        assert plan["source_sha256"] == SOURCE
    if args.batch in {"coefficient-map-injectivity", "coefficient-map-partial-fractions", "coefficient-map-reflection", "coefficient-map-finite-sum", "coefficient-map-summation", "coefficient-map-aggregate", "coefficient-map-telescoper", "coefficient-map-kernel-bridge"}:
        expected_dependencies = {"Definitions/Def_ZetaNine_CoefficientMap.lean", "Definitions/Def_ZetaNine_CoefficientMapJet.lean"}
        if args.batch in {"coefficient-map-partial-fractions", "coefficient-map-reflection", "coefficient-map-finite-sum", "coefficient-map-summation", "coefficient-map-aggregate", "coefficient-map-telescoper", "coefficient-map-kernel-bridge"}:
            expected_dependencies.add("Definitions/Def_ZetaNine_CoefficientMapInjectivity.lean")
        if args.batch in {"coefficient-map-reflection", "coefficient-map-finite-sum", "coefficient-map-summation", "coefficient-map-aggregate", "coefficient-map-telescoper", "coefficient-map-kernel-bridge"}:
            expected_dependencies.add("Definitions/Def_ZetaNine_CoefficientMapPartialFractions.lean")
        if args.batch in {"coefficient-map-finite-sum", "coefficient-map-summation", "coefficient-map-aggregate", "coefficient-map-telescoper", "coefficient-map-kernel-bridge"}:
            expected_dependencies.add("Definitions/Def_ZetaNine_HarmonicStability.lean")
        if args.batch in {"coefficient-map-summation", "coefficient-map-aggregate", "coefficient-map-telescoper", "coefficient-map-kernel-bridge"}:
            expected_dependencies.add("Definitions/Def_ZetaNine_CoefficientMapReflection.lean")
            expected_dependencies.add("Definitions/Def_ZetaNine_CoefficientMapFiniteSum.lean")
        if args.batch in {"coefficient-map-aggregate", "coefficient-map-telescoper", "coefficient-map-kernel-bridge"}:
            expected_dependencies.add("Definitions/Def_ZetaNine_CoefficientMapSummation.lean")
        if args.batch in {"coefficient-map-telescoper", "coefficient-map-kernel-bridge"}:
            expected_dependencies.add("Definitions/Def_ZetaNine_CoefficientMapAggregate.lean")
        if args.batch == "coefficient-map-kernel-bridge":
            expected_dependencies.add("Definitions/Def_ZetaNine_CoefficientMapTelescoper.lean")
            expected_dependencies.add("Definitions/Def_ZetaNine_CoefficientMapShiftDegree.lean")
        assert {r["root_relative"] for r in plan["required_existing_Definitions"]} == expected_dependencies
        for required in plan["required_existing_Definitions"]:
            assert digest(ROOT / required["root_relative"]) == required["sha256"]
    if args.batch == "coefficient-map-matrix":
        names = {"CoefficientMap", "CoefficientMapJet", "CoefficientMapInjectivity",
            "CoefficientMapPartialFractions", "CoefficientMapReflection", "CoefficientMapFiniteSum",
            "CoefficientMapSummation", "CoefficientMapAggregate", "CoefficientMapTelescoper",
            "CoefficientMapShiftDegree", "HarmonicStability", "CoefficientMapKernelBridge"}
        expected = {"Definitions/Def_ZetaNine_" + name + ".lean" for name in names}
        assert {r["root_relative"] for r in plan["required_existing_Definitions"]} == expected
        for row in plan["required_existing_Definitions"]:
            path = ROOT / row["root_relative"]
            assert path.stat().st_size == row["bytes"] and digest(path) == row["sha256"]
    assert plan["overwrite_allowed"] is False
    if args.batch in {"coefficient-map-shift-degree", "coefficient-map-connection"}:
        assert plan["required_existing_Definitions"] == []
    if args.batch == "coefficient-map-jet":
        required = plan["required_existing_Base_definition"]
        assert required["root_relative"] == "Definitions/Def_ZetaNine_CoefficientMap.lean"
        assert digest(ROOT / required["root_relative"]) == required["sha256"]
    assert len(plan["files"]) == 7
    copies = []
    for row in plan["files"]:
        relative = row["root_relative_destination"]
        parts = PurePosixPath(relative).parts
        assert len(parts) == 2 and parts[0] in {"Definitions", "Theorems", "Solutions"}
        assert parts[1].startswith({"Definitions": "Def_" + stem,
            "Theorems": "Thm_" + stem + "_", "Solutions": "Sol_" + stem + "_"}[parts[0]])
        assert parts[1].endswith(".lean") and ".." not in parts
        source = TASK / row["staged_task_relative"]
        assert source.resolve().is_relative_to((OUT / "staged").resolve())
        assert digest(source) == row["sha256"] and source.stat().st_size == row["bytes"]
        destination = ROOT / relative
        assert destination.resolve().is_relative_to(ROOT.resolve())
        data = source.read_bytes()
        if destination.exists():
            assert destination.read_bytes() == data, "Preserving differing existing module: " + relative
        copies.append((source, destination, data, row))
    installed = []
    for source, destination, data, row in copies:
        existed = destination.exists()
        if not existed:
            destination.parent.mkdir(parents=True, exist_ok=True)
            destination.write_bytes(data)
        assert destination.read_bytes() == data
        installed.append({**row, "already_identical": existed, "installed_bytes_match": True})
    scope_path = TASK / "scope.json"
    scope = load(scope_path)
    for relative in [r["root_relative_destination"] for r in plan["files"]] + [Path(__file__).resolve().relative_to(ROOT).as_posix()]:
        if relative not in scope["sources"]:
            scope["sources"].append(relative)
    for row in plan["files"]:
        relative = row["root_relative_destination"]
        if relative.startswith("Solutions/") and relative not in scope["build"]:
            scope["build"].append(relative)
    scope_path.write_text(json.dumps(scope, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    results = {}
    for mode in ("check", "build"):
        command = [sys.executable, str(ROOT / "scripts/workspace.py"), mode]
        if mode == "build":
            command.append("zeta9")
        with (OUT / ("task-" + mode + ".log")).open("w", encoding="utf-8") as log:
            result = subprocess.run(command, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT, check=False)
        (OUT / ("task-" + mode + "-exit.txt")).write_text(str(result.returncode) + "\n", encoding="utf-8")
        results[mode] = result.returncode
        print(f"{args.batch} scoped task {mode}: exit {result.returncode}", flush=True)
    receipt = {"frozen_author_audit_sha256": AUTHOR, "frozen_root_copy_plan_sha256": PLAN,
        "copies": installed, "results": results, "root_bytes_match_frozen_stage": True,
        "new_three_solutions_have_no_Theorems_import": True,
        "other_PNT_root_mirror_remains_type_integration_only": True,
        "batch": args.batch,
        "full_F_invertibility_proved": args.batch in {"coefficient-map-kernel-bridge", "coefficient-map-matrix"},
        "full_F_invertibility_scope": "original p=9,q=1,m=n,d=0, even n>=2, rational quartic" if args.batch in {"coefficient-map-kernel-bridge", "coefficient-map-matrix"} else None,
        "explicit_actual_F_matrix_and_rational_inverse_row_proved": args.batch == "coefficient-map-matrix",
        "general_parameter_F_invertibility_proved": False, "integral_multiplier_inverse_proved": False,
        "original_connection_system_proved": args.batch == "coefficient-map-connection",
        "actual_rational_function_parameter_transport_proved": False,
        "actual_five_output_parameter_transport_proved": False}
    (OUT / "root-install-receipt.json").write_text(json.dumps(receipt, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    raise SystemExit(results["build"])


if __name__ == "__main__":
    main()
