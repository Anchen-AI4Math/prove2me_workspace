# Final v4 interface for Root's network executor

The four current outputs, all under this directory, are:

| File | Schema | SHA256 |
|---|---|---|
| definitions-request-v4.json | `[one complete submit-definition payload]` | b3de7abb267f0b965565d770caafcf9c09605405ace3c6c6e83291d4a6b9448d |
| problems-request-v4.json | `{env, private:false, problems:[three complete registration payloads]}` | c6c4572470d1aad9feb307f6aee3ba029ac04dd1a9c2b9c283d0f92217fc3b2e |
| proof-explanations-v4.json | `{qualified_theorem_name: explanation_string}` | 43f9167fcff5e507ebace01211ddbf72c571ff1c649b505036acfc2609ec9b7d |
| prepared-publication-v4.json | exact seven payloads, seven planned POSTs, six document pins, author/source/evidence contract, blocked independent gate | ec831fe3b832805e53292211aea5fac9723ebe5a29f3be9d0cfd91e427b35883 |

`interface-bindings-v4.json`, SHA256
`e107523caea03d1af5242312f9f9f1b3e0d3494039bc619b7257a29ff0a0536a`,
binds these four interfaces, the final metadata, offline builder and pure gate.
The v1, v2 and v3 artifacts remain preserved. No further metadata version is
planned. `publication-plan.md` supplies the endpoint/WAL/history-resume plan;
its v2 file references are superseded by this final v4 interface.

The builder `prepare_publication_v4.py` has actually executed successfully.
Its state is **waiting for a real Root independent pin**, not publication PASS.
`required-future-Root-pin-v4.json` is a contract, not a manufactured pin.
The independent report hash remains null. No API, Lean, credential read, Root
module installation, mission link or proposal mutation occurred here.

All seven Lean payloads retain the exact staged bytes. The definition JSON
contains those exact UTF-8 bytes as its full definition string. The three
registration payloads retain every original field except the natural language
statement and source citation. In particular, their complete formal_statement,
preamble and theorem_name are unchanged. The Solutions are full direct proofs;
Root may upload from PF/staged after matching the same seven pins, without
installing shared Root modules.

The three explanations contain one background definition, a displayed target,
one Taylor-order-nine/coprime-factor/divisibility/degree argument, followed by
regular-point evaluation or the linear difference argument as appropriate.
There are no upload/import implementation notes or October-release historical
remarks. Source fields cite the actual original 2026-10-04 research pathname,
Lean pathname, exact declaration and full SOURCE hash.

The pure pre-publication gate is:

```powershell
& 'C:\Users\anche\AppData\Local\Programs\Python\Python312\python.exe' `
  formalization/platform/coefficient-map-numerator-pf/publication-preparation-2026-10-07/final_gate_v4.py `
  '<actual future Root independent pin path>'
```

It constructs no network client. It fails when the real pin is missing, then
after a pin exists requires complete author and independent binding rehashes,
all seven SOURCE payloads and the exact final interface. Unknown independent
schema or missing canonical definition-body readback requires a new reviewed
gate adapter; a PASS or a field must never be invented.

Root's separate executor must verify the six matching official document pins
before applying the runtime-only VERSION=0.12.1 override. Every business POST
requires a durable exact-wire-body intent and no blind retry. The fixed new
proposal is read-only and frozen In review. Global public PF acceptance is
recorded separately from unchanged proposal references: 88/18/69/67 remain
the proposal checkpoint; three globally accepted PF proofs would be unreferenced
and increase saved global complete proof receipts from 54 to 57.
