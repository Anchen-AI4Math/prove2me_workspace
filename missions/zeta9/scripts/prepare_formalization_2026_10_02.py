"""Offline packaging of checked proofs into stable platform module paths.

This script never reads credentials and never performs a platform operation.
The dated research ZIP is immutable; new proof modules are a separate batch.
"""
from __future__ import annotations

import json
import re
from pathlib import Path

TASK = Path(__file__).resolve().parents[1]
WORKSPACE = TASK.parents[1]
OUT = TASK / "formalization/platform"
ENV = "0df444a360eaa60ab8c11dca51a86af692955474"
SOURCE_RELEASE = "https://github.com/Anchen0823/zeta9-research-notes/releases/tag/research-2026-10-02"


def write(path: Path, text: str):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text.rstrip() + "\n", encoding="utf-8")


def lean_code(text):
    return "\n".join(line for line in text.splitlines() if not line.startswith("#print axioms"))


def without_definition(text, name):
    # Each checked definition is a small top-level block terminated by a blank line.
    pattern = rf"(?m)^(?:noncomputable )?def {re.escape(name)}\b[\s\S]*?(?=\n\n)"
    match = re.search(pattern, text)
    assert match, name
    start = match.start()
    doc = text.rfind("/--", 0, start)
    if doc >= 0:
        doc_end = text.find("-/", doc) + 2
        if not text[doc_end:start].strip():
            start = doc
    return text[:start] + text[match.end():]


def definition(name, title, code, statement, source):
    path = WORKSPACE / f"Definitions/Def_{name}.lean"
    write(path, code)
    return {"definition_name": name, "definition_title": title, "definition": code,
            "natural_language_statement": statement, "source": source,
            "tags": ["number-theory", "zeta-function", "formalization"],
            "env": ENV, "private": False, "local_path": path.relative_to(WORKSPACE).as_posix()}


def problem(core, namespace, short_name, def_name, title, natural, source, explanation, extra_binders=""):
    code = lean_code(core)
    match = re.search(rf"(?m)^theorem {re.escape(short_name)}\b([\s\S]*?)\s*:=", code)
    assert match, short_name
    signature = extra_binders + match.group(1)
    full_name = namespace + "." + short_name
    preamble = "\n".join(line for line in code.splitlines() if line.startswith("import "))
    preamble += "\nopen scoped BigOperators\nopen Filter\nopen " + namespace + "\n"
    if namespace == "ZetaNine.CenterDenominator":
        preamble = preamble.replace("open ZetaNine.CenterDenominator\n", "")
        preamble += "open ZetaNine.GramContent\n"
    # Filter is only needed for the actual sequence statements. It is not loaded
    # by the integer-only development.
    if "HarmonicStability" not in namespace:
        preamble = preamble.replace("open Filter\n", "")
    formal = f"theorem {full_name}{signature} := by sorry"
    reference = WORKSPACE / f"Theorems/Thm_{full_name.replace('.', '_')}.lean"
    write(reference, preamble + "\nset_option autoImplicit false\n\n" + formal)
    proof_name = "checked_" + short_name
    code = re.sub(rf"\b{re.escape(short_name)}\b", proof_name, code)
    extra_open = "open ZetaNine.GramContent\n" if namespace == "ZetaNine.CenterDenominator" else ""
    solution = code + "\n\nopen " + namespace + "\n" + extra_open + "\ntheorem solution" + signature + " := by\n"
    solution += f"  exact {namespace}.{proof_name}" + "\n\n#print axioms solution\n"
    # Use `exact ...` with explicit arguments below; Lean will not apply a
    # universally quantified constant to newly introduced explicit binders.
    arguments = {
        "primitive_row_gram_gcd_dvd_scaled_saturated": "u v Δ hprimitive hΔ hminor",
        "first_n_derivative_sum_zero": "n r hr",
        "harmonic_den_dvd_lcm_power": "s N",
        "log_den_error_tendsto_zero": "l h r scale hscale hr",
        "log_den_rate_stability": "l h r scale hscale a hh hr",
        "primitive_center_denominator_divisor": "u v a b Δ hprimitive ha hΔ hminor",
    }[short_name]
    solution = solution.replace(f"  exact {namespace}.{proof_name}\n", f"  exact {namespace}.{proof_name} {arguments}\n")
    path = WORKSPACE / f"Solutions/Sol_{full_name.replace('.', '_')}.lean"
    write(path, solution)
    return {"theorem_name": full_name, "theorem_title": title,
            "formal_statement": formal, "natural_language_statement": natural,
            "preamble": preamble, "source": source,
            "tags": ["number-theory", "zeta-function", "formalization"],
            "local_solution": path.relative_to(WORKSPACE).as_posix(),
            "local_reference": reference.relative_to(WORKSPACE).as_posix(),
            "definition_dependency": def_name, "explanation": explanation}


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    definitions = []
    problems = []

    gram = (TASK / "formalization/GramContent.lean").read_text(encoding="utf-8")
    marker = "/-- A Bézout certificate"
    definition_code = gram.split(marker)[0].replace("import Mathlib.Tactic.Ring\n", "")
    definition_code += "\nend ZetaNine.GramContent\n"
    gram_name = "ZetaNine_GramContent"
    gram_source = SOURCE_RELEASE + "; research/direction-arithmetic-next-2026-10-02.md, section 1, equations (1) and (5)."
    definitions.append(definition(gram_name, "Integral row Gram data and divided determinant", definition_code,
        r"For integral rows $u,v$ in any finite dimension, define their scalar product $C=\sum_i u_i v_i$, squared norms $T=\sum_i u_i^2$, $R=\sum_i v_i^2$, and the integer quotient $D_\Delta=(TR-C^2)/\Delta^2$. Integer division is used at the definition level; the companion theorem proves exact division when $u$ is primitive and $\Delta$ divides every minor. No primitivity, divisibility or positivity assumption is built into these definitions.", gram_source))
    gram = "import Definitions.Def_" + gram_name + "\n" + gram.split(marker)[0].split("namespace ZetaNine.GramContent")[0] + (
        "\nnamespace ZetaNine.GramContent\n"
        "variable {ι : Type*} [Fintype ι]\n\n" + marker + gram.split(marker, 1)[1])
    problems.append(problem(gram, "ZetaNine.GramContent", "primitive_row_gram_gcd_dvd_scaled_saturated", gram_name,
        "Primitive-row Gram content divides the scaled divided determinant",
        r"Let $u,v\in\mathbb Z^d$, with $u$ primitive, and let $\Delta\ne0$ divide every minor $u_iv_j-u_jv_i$. Put $T=\langle u,u\rangle$, $C=\langle u,v\rangle$, $R=\langle v,v\rangle$ and $D_\Delta=(TR-C^2)/\Delta^2$. Then" + "\n\n" + r"$$\gcd(T,C)\mid \Delta D_\Delta.$$" + "\n\n" + r"Primitivity means that the coordinates of $u$ admit an integral Bézout combination equal to one. The theorem covers every finite dimension and every nonzero common minor divisor, including the exterior content. It does not assume squarefreeness, linear independence or nondegeneracy modulo any prime.", gram_source,
        r"An integral Bézout certificate for $u$ gives an integer $\lambda$ and an integral row $w$ with $v=\lambda u+\Delta w$. Thus the Gram determinant is exactly $\Delta^2(T\langle w,w\rangle-\langle u,w\rangle^2)$. Writing $G=\gcd(T,C)$, the scalar-product identity shows $G\mid\Delta\langle u,w\rangle$, while $G\mid T$. Subtracting the two resulting divisible terms yields $G\mid\Delta D_\Delta$. This also proves that the displayed integer division is exact.",
        " {ι : Type*} [Fintype ι]"))

    center = (TASK / "formalization/CenterDenominator.lean").read_text(encoding="utf-8")
    projection = (TASK / "formalization/ProjectionDenominator.lean").read_text(encoding="utf-8")
    parts = [gram, projection, center]
    imports = list(dict.fromkeys(line for part in parts for line in part.splitlines()
                                if line.startswith("import ") and not line.startswith("import missions.")))
    bodies = ["\n".join(line for line in part.splitlines() if not line.startswith("import ")) for part in parts]
    center = "\n".join(imports) + "\n\n" + "\n\n".join(bodies)
    problems.append(problem(center, "ZetaNine.CenterDenominator", "primitive_center_denominator_divisor", gram_name,
        "Explicit divisor of the content-adjusted center denominator",
        r"Let $u,v\in\mathbb Z^d$, with $u$ primitive, and let $\Delta\ne0$ divide every exterior minor. Put $T=\langle u,u\rangle$, $C=\langle u,v\rangle$ and $D_\Delta=(T\langle v,v\rangle-C^2)/\Delta^2$. For any integers $a\ne0$ and $b$, the center $\xi=bC/(aT)$ satisfies" + "\n\n" + r"$$\frac{T}{\gcd(T,b\Delta D_\Delta)}\mid\operatorname{den}(\xi).$$" + "\n\n" + r"Primitivity guarantees $T>0$. Neither coprimality of $a,b$ nor primitiveness of $v$ is required. For primitive row reductions and their content ratio this is the computable divisor in equation (6). It asserts an exact denominator divisor, not the still-unproved exponential growth needed for the irrationality route.",
        SOURCE_RELEASE + "; research/direction-arithmetic-next-2026-10-02.md, section 2, equation (6).",
        r"Primitivity first gives $T>0$ and the Gram-content divisibility $\gcd(T,C)\mid\Delta D_\Delta$. Writing the reduced center as $P/Q$, cross multiplication implies $T\mid bCQ$. An integral Bézout identity for $T,C$ then gives $T\mid b\gcd(T,C)Q$, hence $T\mid b\Delta D_\Delta Q$. Dividing out $\gcd(T,b\Delta D_\Delta)$ and using coprimality yields the displayed divisor of $Q$. The denominator content coefficient $a$ never contributes to cancellation of old denominator factors.",
        " {ι : Type*} [Fintype ι]"))

    eight = (TASK / "formalization/EightfoldZeros.lean").read_text(encoding="utf-8")
    marker = "/-! ## General algebra"
    eight_name = "ZetaNine_EightfoldZeros"
    eight_def = eight.split(marker)[0] + "\nend ZetaNine.EightfoldZeros\n"
    eight_source = SOURCE_RELEASE + "; research/new-linear-form-route-repair-2026-10-02.md, opening unnumbered definition of R*_n and the following endpoint-zero paragraph."
    definitions.append(definition(eight_name, "Eightfold-zero repaired rational function", eight_def,
        r"For $n\ge0$, define the exact repaired rational function" + "\n\n" + r"$$R_n^*(t)=\frac{(4n)!^2}{n!^8}\frac{\prod_{j=1}^n(t-j)^8}{\prod_{j=0}^{4n}(t+j)^2}.$$" + "\n\n" + r"The definition file contains the scalar prefactor, numerator and denominator polynomials, and their quotient as a real function. The endpoint-zero and derivative theorems are separate proofs. No convergence, sign, asymptotic, content or irrationality assertion is embedded in the definition.", eight_source))
    start = eight.split("namespace ZetaNine.EightfoldZeros")[0]
    # Put the platform import together with the other imports, before section commands.
    start = "import Definitions.Def_" + eight_name + "\n" + start
    eight = start + "namespace ZetaNine.EightfoldZeros\n\n" + marker + eight.split(marker, 1)[1]
    problems.append(problem(eight, "ZetaNine.EightfoldZeros", "first_n_derivative_sum_zero", eight_name,
        "Eightfold zeros eliminate the first n derivative terms",
        r"For the explicit repaired function $R_n^*$, every integer derivative order $0\le r<8$ satisfies" + "\n\n" + r"$$\sum_{j=1}^{n}(R_n^*)^{(r)}(j)=0.$$" + "\n\n" + r"This holds for every natural $n$, including the empty sum at $n=0$. The derivatives are genuine iterated real derivatives of the rational function. In particular the first $n$ leakage terms of the seventh-derivative series vanish exactly. The theorem does not assert convergence, eventual nonvanishing, decay or irrationality.", eight_source,
        r"For each $j\in\{1,\ldots,n\}$ the numerator has a factor $(t-j)^8$, while every denominator factor is strictly positive at $t=j$. Factor this centered power from the rational function. The remaining quotient is smooth near $j$, and the iterated product rule shows that all derivatives of order below eight vanish there. Summing these individual endpoint identities gives the result. The proof establishes the denominator positivity and factor divisibility for all parameters."))

    harmonic = (TASK / "formalization/HarmonicStability.lean").read_text(encoding="utf-8")
    harmonic_name = "ZetaNine_HarmonicStability"
    harmonic_def = (TASK / "formalization/HarmonicStabilityDefinitions.lean").read_text(encoding="utf-8")
    harmonic_source = SOURCE_RELEASE + "; research/harmonic-denominator-stability-2026-10-01.md, section 2 clearing bound and section 3 Lemma 2 / Corollary 3."
    definitions.append(definition(harmonic_name, "Generalized harmonic sums and actual log denominators", harmonic_def,
        r"For a rational number $q$, define $\ell(q)=\log\operatorname{den}(q)$ using its reduced positive denominator, with $\operatorname{den}(0)=1$. For natural $s,N$, define the actual rational generalized harmonic sum $H_N^{(s)}=\sum_{j=1}^Nj^{-s}$. These are definitions only; the prime-number-theorem growth rate is not assumed.", harmonic_source))
    harmonic = without_definition(without_definition(harmonic, "logDen"), "harmonicPower")
    harmonic = "import Definitions.Def_" + harmonic_name + "\n" + harmonic
    problems.append(problem(harmonic, "ZetaNine.HarmonicStability", "harmonic_den_dvd_lcm_power", harmonic_name,
        "Actual harmonic denominators divide the finite lcm power",
        r"Let $s,N$ be any natural numbers, $H_N^{(s)}=\sum_{j=1}^{N}j^{-s}$, and $L_N=\operatorname{lcm}(1,\ldots,N)$, with $L_0=1$. Then" + "\n\n" + r"$$\operatorname{den}(H_N^{(s)})\mid L_N^s.$$" + "\n\n" + r"The result concerns the reduced denominator of the actual harmonic sum. It includes $s=0$ and $N=0$ and supplies the finite clearing bound used in the arithmetic argument. It makes no lower-bound or asymptotic prime-distribution assertion.", harmonic_source,
        r"For each $1\le j\le N$, the denominator of $j^{-s}$ is $j^s$, which divides $L_N^s$. The reduced denominator of a sum divides the least common multiple of the summands' denominators. Finite induction therefore proves the same common clearing bound for the actual harmonic sum, including all possible numerator cancellations."))
    problems.append(problem(harmonic, "ZetaNine.HarmonicStability", "log_den_error_tendsto_zero", harmonic_name,
        "Subexponential rational perturbations preserve normalized denominator error",
        r"Let $h_i,r_i$ be arbitrary rational families along a filter and let $s_i\ge0$ be a real scale. If $\ell(r_i)/s_i\to0$, then" + "\n\n" + r"$$\frac{\ell(h_i+r_i)-\ell(h_i)}{s_i}\longrightarrow0.$$" + "\n\n" + r"No limiting rate or sign condition is assumed for $h_i$. Here $\ell$ is the logarithm of the actual reduced denominator. This is the unconditional stability mechanism; it does not prove the separate harmonic prime-number-theorem baseline.", harmonic_source,
        r"The two denominator divisibilities give $|\ell(h+r)-\ell(h)|\le\ell(r)$ for every rational $h,r$. Divide by the nonnegative scale and apply the squeeze theorem. The bound follows from actual reduced denominators and hence remains valid after arbitrary numerator cancellation. No baseline convergence assumption is used."))
    problems.append(problem(harmonic, "ZetaNine.HarmonicStability", "log_den_rate_stability", harmonic_name,
        "Rational perturbations transfer an established denominator growth rate",
        r"Let $h_i,r_i$ be rational families along a filter, let $s_i\ge0$, and let $\alpha\in\mathbb R$. If $\ell(h_i)/s_i\to\alpha$ and $\ell(r_i)/s_i\to0$, then" + "\n\n" + r"$$\frac{\ell(h_i+r_i)}{s_i}\longrightarrow\alpha.$$" + "\n\n" + r"The conclusion transfers an already established baseline rate; that baseline is an explicit hypothesis, not a new axiom. Applied to generalized harmonic sums it is the stability part of the original corollary, and leaves their PNT-dependent baseline proof as a separate task.", harmonic_source,
        r"The exact logarithmic denominator inequality bounds the distance between the normalized perturbed and unperturbed rates by $\ell(r_i)/s_i$. This bound tends to zero. Since the unperturbed rate tends to $\alpha$, the perturbed rate has the same limit. The hypotheses include precisely the baseline rate being transferred and the subexponential denominator condition on the perturbation."))

    for item in problems:
        if item["theorem_name"].endswith(("log_den_error_tendsto_zero", "log_den_rate_stability")):
            item["natural_language_statement"] += "\n\n" + (
                r"**Formalization Note.** The statement also permits zero scale, using Lean's total real division convention $x/0=0$. On strictly positive scales it is the ordinary mathematical quotient. The harmonic application uses scale $N$, which is positive eventually."
            )
    write(OUT / "definitions-request.json", json.dumps(definitions, ensure_ascii=False, indent=2))
    write(OUT / "problems-request.json", json.dumps({"env": ENV, "private": False, "problems": problems}, ensure_ascii=False, indent=2))
    scope_path = TASK / "scope.json"
    scope = json.loads(scope_path.read_text(encoding="utf-8"))
    new_sources = ["missions/zeta9/formalization/**/*", "missions/zeta9/verification/formalization-*/**/*",
                   "missions/zeta9/scripts/prepare_formalization_2026_10_02.py"]
    new_sources += [row["local_path"] for row in definitions]
    new_sources += [p["local_solution"] for p in problems] + [p["local_reference"] for p in problems]
    scope["sources"] = list(dict.fromkeys(scope["sources"] + new_sources))
    scope["build"] = list(dict.fromkeys(scope["build"] + [p["local_solution"] for p in problems]))
    write(scope_path, json.dumps(scope, ensure_ascii=False, indent=2))
    print(f"Prepared {len(definitions)} lightweight definitions and {len(problems)} exact proof targets; no API calls.")


if __name__ == "__main__":
    main()
