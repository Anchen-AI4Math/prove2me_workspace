"""Mechanical PNT staging from executed Lean declaration and syntax facts.

Source locations, proof boundaries, imports and diagnostic cuts are exclusively
the byte ranges reported by the two official Lean oracles. Their parser input
is persisted. No regex or source-text search decides a mathematical cut.
"""
from pathlib import Path
import hashlib, json, sys

sys.stdout.reconfigure(encoding="utf-8")
OUT = Path(__file__).resolve().parent
TASK = OUT.parents[2]
ROOT = TASK.parents[1]
NS = "ZetaNine.HarmonicStability"
REV = "0df444a360eaa60ab8c11dca51a86af692955474"
NAMES = ["psi_pnt_rate", "harmonic_log_den_rate", "harmonic_nine_double_log_den_rate",
         "harmonic_perturbed_log_den_rate"]
TARGETS = [NS+"."+x for x in NAMES]
ARGS = ["", "s hs", "", "s hs r hr"]
DEFS = {NS+"."+x for x in ["logDen","harmonicPower","primeRemainder","harmonicExceptionalProduct"]}
ORDER = ["Solutions.Sol_ZetaNine_HarmonicStability_harmonic_den_dvd_lcm_power",
         "missions.zeta9.formalization.HarmonicPrimeValuation",
         "missions.zeta9.formalization.HarmonicAsymptotic",
         "missions.zeta9.formalization.PNTTransfer"]

def load(p):
    return json.loads(p.read_text(encoding="utf-8-sig"))
def sha(data):
    return hashlib.sha256(data).hexdigest()
def write(p, data):
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_bytes(data if isinstance(data, bytes) else data.encode("utf-8"))
def dump(p, obj):
    write(p, json.dumps(obj, ensure_ascii=False, indent=2)+"\n")
def jsonl(p):
    return [json.loads(x) for x in p.read_text(encoding="utf-8-sig").splitlines() if x.startswith("{")]
def edit(data, edits):
    edge = len(data)
    for start, end, value in sorted(set(edits), reverse=True):
        assert 0 <= start <= end <= edge, (start,end,edge)
        data = data[:start]+value+data[end:]
        edge = start
    return data

graph = jsonl(OUT/"decl-graph.jsonl")
by_name = {x["name"]:x for x in graph}
assert len(by_name) == len(graph)
readback = load(OUT/"medium-pnt-proved-readback.json")
assert (readback["theorem_id"],readback["status"],readback["mathlib_rev"]) == (
    "7cfa31c8-4063-4b52-81fc-8b2f2a59495e","Proved",REV)
reachable, frontier = set(), list(TARGETS)
# Include every instance in the actual participating source modules.
old_plan = load(OUT/"reachable-local-graph.json")
frontier += [r["name"] for r in graph if r["isInstance"] and r["module"] in old_plan["participating_source_modules"]]
while frontier:
    n = frontier.pop()
    if n in reachable:
        continue
    reachable.add(n)
    assert n in by_name, n
    if n == "MediumPNT":
        continue
    row = by_name[n]
    frontier += row["typeDeps"]+row["valueDeps"]
selected = [by_name[n] for n in sorted(reachable) if n != "MediumPNT" and by_name[n]["startLine"] > 0]
modules = sorted({x["module"] for x in selected})
assert set(modules) <= set(old_plan["participating_source_modules"]), modules
receipt = {x["module"]:x for x in load(OUT/"stage2-extract-receipt.json")}
sources, facts, joins = {}, {}, {}
for module in modules:
    record = receipt[module]
    disk = Path(record["source"]).read_bytes()
    oracle = Path(record["oracle_input"]).read_bytes()
    assert sha(disk) == record["source_sha256"]
    assert sha(oracle) == record["oracle_input_sha256"]
    assert oracle == disk.replace(b"\r\n",b"\n")
    sources[module] = oracle
    facts[module] = jsonl(OUT/(module.replace(".","_")+"-sketch.jsonl"))
    decls = [x for x in facts[module] if x["kind"] == "decl"]
    for row in selected:
        if row["module"] != module:
            continue
        candidates = [f for f in decls if f["declStart"]["line"] <= row["startLine"] <= f["declEnd"]["line"]]
        assert len(candidates) == 1, (row,candidates)
        fact = candidates[0]
        assert fact["valStart"] is not None, row
        joins[row["name"]] = {"graph":row,"stage2":fact,
            "proof_lines":fact["declEnd"]["line"]-fact["valStart"]["line"]+1,
            "placement":"existing-public-definition" if row["userName"] in DEFS else "inline-solution"}

imports, fragments, cuts = set(), [], []
for module in ORDER:
    source = sources[module]
    keep_spans = {(j["stage2"]["declStart"]["offset"],j["stage2"]["declEnd"]["offset"])
                  for j in joins.values() if j["graph"]["module"] == module
                  and j["placement"] == "inline-solution"}
    edits = []
    for f in facts[module]:
        if f["kind"] == "decl":
            span = (f["declStart"]["offset"],f["declEnd"]["offset"])
            if span not in keep_spans:
                edits.append((*span,b""))
                cuts.append({"module":module,"reason":"unselected or existing-definition declaration","fact":f})
        elif f["kind"] == "import":
            mod = f["module"]
            if mod.startswith("Mathlib."):
                imports.add(mod)
            else:
                assert mod in [*ORDER,"Definitions.Def_ZetaNine_HarmonicStability","PrimeNumberTheoremAnd.MediumPNT"], mod
            span = f["span"]
            edits.append((span["start"]["offset"],span["end"]["offset"],b""))
            cuts.append({"module":module,"reason":"parser-certified import relocation","fact":f})
        elif f["kind"] == "command" and f["syntaxKind"] == "Lean.Parser.Command.printAxioms":
            span = f["span"]
            edits.append((span["start"]["offset"],span["end"]["offset"],b""))
            cuts.append({"module":module,"reason":"diagnostic print removal","fact":f})
    fragments.append(edit(source,edits).decode("utf-8"))

# Preserve all source namespace, variable, local notation, option and open commands.
headers = ["Definitions.Def_ZetaNine_HarmonicStability",
           "Definitions.Def_ZetaNine_HarmonicPrimeValuation","Theorems.Thm_MediumPNT"]+sorted(imports)
core = "\n".join("import "+m for m in headers)+"\n\n"+"\n\n".join(fragments)
write(OUT/"proof-core.lean",core)
planned = {"targets":TARGETS,"reachable_with_boundary":len(reachable),
           "selected_source_declarations":len(selected),"new_public_definitions":[],
           "participating_source_modules":modules,"selected_declarations":joins,
           "reused_public_definitions":sorted(DEFS),"source_receipts":list(receipt.values()),
           "all_instance_roots":[r["name"] for r in graph if r["isInstance"] and r["module"] in modules],
           "boundary":readback,"cuts":cuts,"regex_source_position_queries":False,
           "unselected_original_global_solution_deleted":True,
           "native_clearing_proof_inlined":True,
           "public_node_choice":"Four original endpoint declarations; reachable helpers stay inside full Solutions, existing actual definitions are imported."}
dump(OUT/"decl-plan.json",planned)

preamble = "\n".join("import "+m for m in ["Definitions.Def_ZetaNine_HarmonicStability",
    "Definitions.Def_ZetaNine_HarmonicPrimeValuation","Mathlib.NumberTheory.Chebyshev"])+"\n\nset_option autoImplicit false\nopen Filter\nopen "+NS+"\n"
titles = ["The actual Chebyshev psi prime-number-theorem rate",
          "The reduced generalized harmonic denominator has rate equal to its positive order",
          "The reduced ninth harmonic denominator has rate eighteen at double endpoints",
          "Small-denominator perturbations preserve the unconditional harmonic denominator rate"]
nl = [
    "The actual Chebyshev function satisfies $\\psi(x)/x\\to1$ as the real variable $x\\to+\\infty$. This theorem has no hypotheses. It derives the limit from the already proved MediumPNT error estimate for the actual $\\psi$, with a positive constant and relative error $\\exp(-c(\\log x)^{1/10})$ tending to zero.",
    "For every fixed positive natural number $s$, write $H_N^{(s)}=\\sum_{j=1}^N j^{-s}$ in lowest terms. Then $\\log\\operatorname{den}(H_N^{(s)})/N\\to s$ along all natural $N\\to\\infty$. The only hypothesis is $s>0$. The prime-number-theorem inputs and the harmonic baseline are proved in the complete solution rather than assumed.",
    "For the actual rational ninth-order harmonic sum at the double endpoint, $\\log\\operatorname{den}(H_{2M}^{(9)})/M\\to18$ as $M\\to\\infty$ through natural numbers. There are no hypotheses; the factor eighteen is nine times the exact endpoint scaling factor two. This supplies the harmonic denominator baseline in the right-shifted Mellin construction.",
    "For every fixed positive natural order $s$ and every rational sequence $r_N$ such that $\\log\\operatorname{den}(r_N)/N\\to0$, one has $\\log\\operatorname{den}(H_N^{(s)}+r_N)/N\\to s$. The perturbation is arbitrary subject to its stated sublinear logarithmic denominator condition. The harmonic baseline and prime-number-theorem inputs are proved; they are not extra hypotheses."
]
explanation = "The unchanged original proof derives psi/x→1 from the genuine MediumPNT estimate. Mathlib's proved psi−theta=O(sqrt x) and psi(N)=log(lcmUpto N) supply both PNT inputs. The harmonic denominator is bounded above by lcmUpto(N)^s, using the complete clearing proof inline. At every fixed finite-block cutoff K, the actual prime valuations force large primes to exponent s in the reduced denominator once finitely many prefix exceptions are excluded. Chebyshev block sums give the lower rate sK/(K+1); letting K increase squeezes the full natural sequence to s. The exact double-endpoint theorem specializes to s=9 and scales by two. Rational addition/subtraction denominator divisibility proves |log den(q+r)−log den(q)|≤log den(r), so the stated small-denominator condition gives the original perturbation endpoint. All native proofs close with only propext, Classical.choice and Quot.sound; the platform version imports the already Proved MediumPNT, whose local statement mirror is explicitly not a proof. No irrationality or J-condition conclusion is claimed."
problems, provenance = [], {}
for index, name in enumerate(NAMES):
    full = NS+"."+name
    fact = joins[full]["stage2"]
    source = sources[joins[full]["graph"]["module"]]
    dstart,dend,vstart = [fact[k]["offset"] for k in ["declStart","declEnd","valStart"]]
    refs = [r for r in facts[joins[full]["graph"]["module"]] if r["kind"] == "ref" and r["const"] == full]
    bindings = [r for r in refs if dstart <= r["start"]["offset"] < vstart]
    assert len(bindings) == 1, (full,bindings)
    bind = bindings[0]
    bstart,bend = bind["start"]["offset"],bind["end"]["offset"]
    assert source[bstart:bend].decode("utf-8") == name
    signature = source[bend:vstart].decode("utf-8")
    edits = [(bstart-dstart,bend-dstart,full.encode("utf-8"))]
    if fact["docstring"]:
        span = fact["docstring"]
        edits.append((span["start"]["offset"]-dstart,span["end"]["offset"]-dstart,b""))
    formal = edit(source[dstart:vstart],edits).decode("utf-8").strip()+":= by sorry"
    sol_path = "Solutions/Sol_"+full.replace(".","_")+".lean"
    ref_path = "Theorems/Thm_"+full.replace(".","_")+".lean"
    solution = core+"\n\nopen "+NS+"\n\ntheorem solution"+signature+":= by\n  exact "+full+(" "+ARGS[index] if ARGS[index] else "")+"\n\n#print axioms solution\n"
    reference = preamble+"\n"+formal+"\n"
    write(OUT/"staged"/sol_path,solution)
    write(OUT/"staged"/ref_path,reference)
    source_record = receipt[joins[full]["graph"]["module"]]
    problems.append({"theorem_name":full,"theorem_title":titles[index],
        "formal_statement":formal,"natural_language_statement":nl[index],"preamble":preamble,
        "source":"https://github.com/Anchen0823/zeta9-research-notes/releases/tag/research-2026-10-02; research/harmonic-denominator-stability-2026-10-01.md, sections 2 and 3; research/mellin-shift-arithmetic-2026-10-01.md. Original verified Lean source: missions/zeta9/formalization/PNTTransfer.lean, lines "+str(fact["declStart"]["line"])+"–"+str(fact["declEnd"]["line"])+", SHA256 "+source_record["source_sha256"]+".",
        "tags":["number-theory","asymptotics","harmonic-numbers","formalization"],
        "explanation":explanation,"local_solution":sol_path,"local_reference":ref_path,
        "verified_local_theorem":full,"definition_dependencies":["ZetaNine_HarmonicStability","ZetaNine_HarmonicPrimeValuation"],
        "proved_theorem_dependencies":[{"theorem_name":"MediumPNT","theorem_id":readback["theorem_id"]}],
        "proof_size_note":"Actual reachable proof declarations retained byte-for-byte; existing definition declarations, unreachable declarations and parser-recorded imports/diagnostics are removed by exact Lean spans. No mathematical proof is rewritten."})
    provenance[full] = {"stage2_declaration_fact":fact,"binding_fact":bind,
        "solution_sha256":sha(solution.encode()),"reference_sha256":sha(reference.encode()),
        "formal_statement_sha256":sha(formal.encode()),"wrapper_arguments":ARGS[index]}

dump(OUT/"problems-request.json",{"env":REV,"private":False,"problems":problems})
dump(OUT/"definitions-request.json",[])
dump(OUT/"integration-provenance.json",{"source_position_authority":"Executed official Stage1+Stage2 Lean oracles; parser-span/snapshot extension only", "targets":provenance,"proof_core_sha256":sha(core.encode()),"imports":headers,"decl_plan":"decl-plan.json","extra_pnt_assumptions":[],"new_public_definitions":[]})

# Identical canonical Solutions are tested against either the explicit type-only
# platform mirror or a forwarding import of the genuinely proved upstream PNT.
mirror = "import Mathlib.NumberTheory.Chebyshev\nimport Mathlib.Analysis.Asymptotics.Lemmas\nimport Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics\nopen scoped Chebyshev\nopen Filter\n\n"+readback["formal_statement"]+"\n"
write(OUT/"boundary-mirror/stub/Theorems/Thm_MediumPNT.lean",mirror)
write(OUT/"boundary-mirror/native/Theorems/Thm_MediumPNT.lean","import PrimeNumberTheoremAnd.MediumPNT\n")
dump(OUT/"boundary-policy.json",{"allowed_proved_boundary":{"theorem_name":"MediumPNT","theorem_id":readback["theorem_id"],"status":"Proved","mathlib_rev":REV},"stub_mirror_is_proof":False,"canonical_typecheck_may_have_sorryAx_only_through_boundary":True,"native_same_solution_bytes_must_have_only_standard_three_axioms":True,"pending_or_unproved_boundaries_allowed":False,"canonical_source_directory":"staged","mirror_directories":{"stub":"boundary-mirror/stub","native":"boundary-mirror/native"},"new_public_definitions":[]})

def report(module, names, output):
    entries = "\n".join('  emit "'+label+'" `'+n for label,n in names)
    return "import "+module+"\nimport Lean\nopen Lean Meta\nset_option pp.fullNames true\nset_option pp.universes false\nrun_meta do\n  let mut rows : Array Json := #[]\n  let emit (label : String) (name : Name) : MetaM Unit := do\n    let ci ← getConstInfo name\n    let typ ← ppExpr ci.type\n    let axioms ← Lean.collectAxioms name\n    let body ← match ci with\n      | .defnInfo d => pure (Json.str (← ppExpr d.value).pretty)\n      | _ => pure Json.null\n    IO.println (Json.mkObj [(\"label\",Json.str label),(\"declaration\",Json.str name.toString),(\"type\",Json.str typ.pretty),(\"axioms\",toJson (axioms.toList.map Name.toString)),(\"definitionValue\",body)]).compress\n"+entries+"\n"

objects = sorted(DEFS)
write(OUT/"types-original.lean",report("missions.zeta9.formalization.PNTTransfer",[(x,x) for x in TARGETS+objects+["MediumPNT"]],"original"))
for i,p in enumerate(problems):
    for kind,decl,field in [("solution","solution","local_solution"),("reference",p["theorem_name"],"local_reference")]:
        module = p[field].removesuffix(".lean").replace("/",".")
        write(OUT/f"types-{i}-{kind}.lean",report(module,[(p["theorem_name"],decl)]+[(x,x) for x in objects]+([("MediumPNT","MediumPNT")] if kind == "solution" else []),kind))
write(OUT/"types-boundary.lean",report("Theorems.Thm_MediumPNT",[("MediumPNT","MediumPNT")],"boundary"))
print(json.dumps({"targets":TARGETS,"reachable":len(reachable),"source_declarations":len(selected),"new_definitions":0,"staged_paths":[p[k] for p in problems for k in ["local_reference","local_solution"]]},ensure_ascii=False,indent=2))
