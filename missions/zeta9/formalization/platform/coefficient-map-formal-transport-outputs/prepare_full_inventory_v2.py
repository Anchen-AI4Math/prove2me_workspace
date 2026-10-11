"""Strengthen uncompiled control SOURCE: full values of all own public helpers."""
import sys
import initialize_author as p


def main():
    sys.stdout.reconfigure(encoding="utf-8")
    old = p.load(p.OUT / "author-control-preparation.json")
    contexts = []
    needle = '''      if name.isInternalDetail || (privateToUserName? name).isSome then
        helpers := name :: helpers
        full name "platform_author_all_generated_complete_type_and_value"
'''
    replacement = '''      match info with
      | .defnInfo _ | .thmInfo _ | .opaqueInfo _ =>
        full name "platform_author_all_actual_complete_type_and_value"
      | _ => pure ()
      if name.isInternalDetail || (privateToUserName? name).isSome then
        helpers := name :: helpers
'''
    for context in old["contexts"]:
        ctx = p.PROJECT / context["tag"]
        source = (ctx / "OutputsPlatformGenerated.lean").read_text(encoding="utf-8")
        assert source.count(needle) == 1
        source = source.replace(needle, replacement, 1)
        p.write(ctx / "OutputsPlatformGeneratedV2.lean", source)
        resolver = (ctx / "OutputsPlatformResolver.lean").read_text(encoding="utf-8")
        assert resolver.count("import OutputsPlatformGenerated\n") == 1
        resolver = resolver.replace("OutputsPlatformGenerated", "OutputsPlatformGeneratedV2")
        p.write(ctx / "OutputsPlatformResolverV2.lean", resolver)
        rows = context["rows"][:2] + [
            {"module": name, "path": name + ".lean", "binding": p.bind(ctx / (name + ".lean"))}
            for name in ["OutputsPlatformGeneratedV2", "OutputsPlatformResolverV2"]]
        contexts.append({**context, "rows": rows, "actual_own_modules": [x.replace("OutputsPlatformGenerated", "OutputsPlatformGeneratedV2") for x in context["actual_own_modules"]],
                         "all_public_named_helpers_have_complete_type_value_inferType_records": True})
    p.dump(p.OUT / "author-control-preparation-v2.json", {**old, "contexts": contexts,
        "original_control_plan": p.bind(p.OUT / "author-control-preparation.json"),
        "all_actual_public_and_generated_declaration_values_recorded": True,
        "weakened_original_header_or_math_domains": False, "proof_source_modified": False,
        "Lean_calls_in_refinement": 0, "API_calls": 0})
    print("Fresh V2 generated controls record every own named/public/internal helper complete type/value/inferType; old controls retained.")


if __name__ == "__main__":
    main()
