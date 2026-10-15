"""Prepare faithful Zipf helper declarations and genuine reduction proofs.

Original platform statements and accepted direct proofs remain untouched.
"""
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
GRAPH = ROOT / "missions/zipf/graph"
ENV = "0df444a360eaa60ab8c11dca51a86af692955474"
BASE = "import Definitions.Def_ZipfLaw_Defs\n\nset_option autoImplicit false\n\nopen ZipfLaw\n\n"
SOURCE = ('Wikipedia, "Zipf\'s law", https://en.wikipedia.org/wiki/Zipf%27s_law, '
          'section "Formal definition"; auxiliary lemma for the original ZipfLaw mission, '
          'derived from its displayed PMF and generalized harmonic sum.')


def write(path, text):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text.rstrip() + "\n", encoding="utf-8")


def signature(name):
    code = (ROOT / f"Theorems/Thm_ZipfLaw_{name}.lean").read_text(encoding="utf-8")
    return code.split(f"theorem {name}", 1)[1].split(" := by sorry", 1)[0].strip()


def main():
    original = (ROOT / "Solutions/Sol_ZipfLaw_zipf_infinite_extension.lean").read_text(encoding="utf-8")
    range_lemma = original.split("private lemma harmonic_range", 1)[1].split("private lemma zipf_summable_iff", 1)[0]
    range_lemma = "private lemma harmonic_range" + range_lemma
    term_lemma = original.split("private lemma real_term_cast", 1)[1].split("theorem solution", 1)[0]
    term_lemma = "private lemma real_term_cast" + term_lemma
    pos = (ROOT / "Solutions/Sol_ZipfLaw_zipfPMF_sum_eq_one.lean").read_text(encoding="utf-8")
    pos_body = pos.split("private lemma zipf_harmonic_pos", 1)[1].split("theorem solution", 1)[0]
    moment = (ROOT / "Solutions/Sol_ZipfLaw_zipfPMF_mean.lean").read_text(encoding="utf-8")
    moment_body = moment.split("private lemma moment_sum", 1)[1].split("theorem solution", 1)[0]

    helpers = [
        {
            "name": "zipf_summable_iff",
            "signature": "(s : ℝ) (hs : 0 ≤ s) :\n    Summable (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ s) ↔ 1 < s",
            "title": "The Zipf p-series converges exactly for $s>1$",
            "statement": r"For a real exponent $s\ge0$, the series $\sum_{k=1}^{\infty} k^{-s}$ is summable if and only if $s>1$. This is the convergence criterion in the infinite-extension theorem, isolated for reuse in both its convergent and divergent branches.",
            "body": "  have h := Real.summable_one_div_nat_add_rpow 1 s\n  have habs : ∀ k : ℕ, |(k : ℝ) + 1| = (k : ℝ) + 1 := fun k =>\n    abs_of_pos (by positivity)\n  simpa only [habs] using h",
            "explanation": r"For every nonnegative exponent $s$, Mathlib's real p-series criterion, applied to the shift $1$, gives summability exactly when $s>1$. Every shifted base $k+1$ is positive, so removing the absolute value in that criterion gives precisely the Zipf series.",
            "dependencies": [],
        },
        {
            "name": "zipf_genHarmonic_tendsto_zeta",
            "signature": "(s : ℝ) (hs : 1 < s) :\n    Filter.Tendsto (fun N : ℕ => ((genHarmonic N s : ℝ) : ℂ)) Filter.atTop\n      (nhds (riemannZeta s))",
            "title": "For $s>1$, the Zipf harmonic sums tend to $\\zeta(s)$",
            "statement": r"If $s>1$, the generalized harmonic partial sums $H_{N,s}=\sum_{k=1}^{N}k^{-s}$ converge to Riemann's zeta function $\zeta(s)$. The formal limit takes place in $\mathbb C$ after casting the real sums, because Mathlib's `riemannZeta` is complex-valued.",
            "prefix": range_lemma + term_lemma,
            "body": "  have hreal := (zipf_summable_iff s (by linarith)).mpr hs\n  have hcomplex := (Complex.hasSum_ofReal).mpr hreal.hasSum\n  have hcomplexSummable : Summable (fun k : ℕ => 1 / (k + 1 : ℂ) ^ (s : ℂ)) :=\n    hcomplex.summable.congr (fun k => real_term_cast k s)\n  have hsum : HasSum (fun k : ℕ => 1 / (k + 1 : ℂ) ^ (s : ℂ)) (riemannZeta s) := by\n    rw [zeta_eq_tsum_one_div_nat_add_one_cpow (by simpa using hs)]\n    exact hcomplexSummable.hasSum\n  have hfn : (fun N : ℕ => ((genHarmonic N s : ℝ) : ℂ)) =\n      (fun N : ℕ => ∑ k ∈ Finset.range N, 1 / (k + 1 : ℂ) ^ (s : ℂ)) := by\n    funext N\n    rw [harmonic_range]\n    simp only [Complex.ofReal_sum]\n    exact Finset.sum_congr rfl (fun k _ => real_term_cast k s)\n  rw [hfn]\n  exact hsum.tendsto_sum_nat",
            "explanation": r"The Zipf convergence criterion supplies a summable real series when $s>1$. Casting its terms to $\mathbb C$ gives the usual complex Dirichlet series, which equals $\zeta(s)$ in this half-plane. Reindexing the finite interval $1,\ldots,N$ as $k+1$ for $k<N$ identifies its partial sums with $H_{N,s}$; the partial-sum limit of the resulting `HasSum` is the assertion.",
            "dependencies": ["zipf_summable_iff"],
        },
        {
            "name": "zipf_genHarmonic_tendsto_atTop",
            "signature": "(s : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1) :\n    Filter.Tendsto (fun N : ℕ => genHarmonic N s) Filter.atTop Filter.atTop",
            "title": "For $0\\le s\\le1$, the Zipf harmonic sums tend to infinity",
            "statement": r"For every real exponent $0\le s\le1$, the generalized harmonic sums $H_{N,s}$ tend to $+\infty$ as $N\to\infty$. In particular no finite normalizing constant can extend these finite Zipf laws to infinitely many ranks.",
            "prefix": range_lemma,
            "body": "  have hnot : ¬Summable (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ s) := by\n    rw [zipf_summable_iff s hs]\n    exact not_lt_of_ge hs1\n  have hdiv := (not_summable_iff_tendsto_nat_atTop_of_nonneg\n    (fun k : ℕ => by positivity : ∀ k : ℕ, 0 ≤ 1 / ((k : ℝ) + 1) ^ s)).mp hnot\n  simpa only [← harmonic_range] using hdiv",
            "explanation": r"The Zipf convergence criterion rules out summability for $s\le1$. Each term is nonnegative, so the partial sums of this nonsummable series tend to $+\infty$. Reindexing the partial sums gives precisely $H_{N,s}$.",
            "dependencies": ["zipf_summable_iff"],
        },
        {
            "name": "genHarmonic_pos",
            "signature": pos_body.split(" := by", 1)[0].strip(),
            "title": "A nonempty generalized harmonic sum is positive",
            "statement": r"For every integer $N\ge1$ and real exponent $s$, the generalized harmonic sum $H_{N,s}=\sum_{k=1}^{N} k^{-s}$ is strictly positive. This ensures that the common normalizing factor can be cancelled and logarithms of supported Zipf probabilities are well-defined.",
            "body": pos_body.split(" := by", 1)[1].strip(),
            "explanation": r"All terms $k^{-s}$ are nonnegative. The sum contains the rank-one term $1^{-s}=1$, because $N\ge1$, and that term is strictly positive. Therefore the entire finite sum is positive.",
            "dependencies": [],
        },
        {
            "name": "zipfPMF_moment",
            "signature": moment_body.split(" := by", 1)[0].strip(),
            "title": "All finite Zipf moments are ratios of shifted harmonic sums",
            "statement": r"For every cutoff $N\in\mathbb N$, real exponent $s$, and integer moment order $p\ge0$, the finite Zipf law satisfies $\sum_{k=1}^{N} k^p f(k;s,N)=H_{N,s-p}/H_{N,s}$. The identity includes $N=0$ under Lean's convention for division by zero. The first and second moment formulas in the mission are its special cases.",
            "body": moment_body.split(" := by", 1)[1].strip(),
            "explanation": r"On the supported ranks $1\le k\le N$, multiplying $f(k;s,N)=k^{-s}/H_{N,s}$ by $k^p$ gives $k^{-(s-p)}/H_{N,s}$. The rank is positive, so the real-power subtraction identity applies. Summing the identity and taking the common denominator outside the sum yields the shifted harmonic ratio. An empty support satisfies the same algebraic identity.",
            "dependencies": [],
        },
    ]
    reductions = [
        {
            "name": "zipf_infinite_extension",
            "dependencies": ["zipf_summable_iff", "zipf_genHarmonic_tendsto_zeta", "zipf_genHarmonic_tendsto_atTop"],
            "body": "  exact ⟨zipf_summable_iff s hs,\n    fun hs1 => zipf_genHarmonic_tendsto_zeta s hs1,\n    fun hs1 => zipf_genHarmonic_tendsto_atTop s hs hs1⟩",
            "explanation": r"The infinite-extension theorem has three substantive clauses. The convergence criterion is `zipf_summable_iff`; when $s>1$, `zipf_genHarmonic_tendsto_zeta` identifies the limit as $\zeta(s)$; when $s\le1$, `zipf_genHarmonic_tendsto_atTop` proves divergence. Their conjunction is exactly the original target. Both limit lemmas themselves reuse the convergence criterion.",
        },
        {
            "name": "zipfPMF_sum_eq_one",
            "dependencies": ["zipfPMF_cdf", "genHarmonic_pos"],
            "body": "  rw [zipfPMF_cdf N hN s N le_rfl]\n  exact div_self (genHarmonic_pos N hN s).ne'",
            "explanation": r"Evaluate the cumulative-distribution identity at its full cutoff $n=N$. It gives total mass $H_{N,s}/H_{N,s}$. Positivity of the nonempty generalized harmonic sum makes this ratio equal to one.",
        },
        {
            "name": "zipfPMF_mean",
            "dependencies": ["zipfPMF_moment"],
            "body": "  simpa only [Nat.cast_one, pow_one] using zipfPMF_moment N s 1",
            "explanation": r"The mean is the moment of order one. Substituting $p=1$ in the general exponent-shift identity gives $\mathbb E[k]=H_{N,s-1}/H_{N,s}$.",
        },
        {
            "name": "zipfPMF_variance",
            "dependencies": ["zipfPMF_moment", "zipfPMF_mean"],
            "body": "  rw [zipfPMF_moment N s 2, zipfPMF_mean N hN s, div_pow]\n  norm_num",
            "explanation": r"Apply the general moment identity with $p=2$ and reuse the proved first-moment formula. Subtracting the square of the mean from the second moment yields $H_{N,s-2}/H_{N,s}-H_{N,s-1}^2/H_{N,s}^2$.",
        },
    ]
    # Reuse the accepted algebraic bodies, replacing duplicate private lemmas
    # with their genuine public dependencies.
    entropy = (ROOT / "Solutions/Sol_ZipfLaw_zipfPMF_entropy.lean").read_text(encoding="utf-8")
    entropy_body = entropy.split("theorem solution", 1)[1].split(" := by", 1)[1].split("#print axioms", 1)[0]
    entropy_body = entropy_body.replace("log_term N s k", "log_zipfPMF_affine N s k")
    entropy_body = entropy_body.replace("pmf_sum N hN s", "zipfPMF_sum_eq_one N hN s")
    reductions.append({"name": "zipfPMF_entropy", "dependencies": ["log_zipfPMF_affine", "zipfPMF_sum_eq_one"],
                       "body": entropy_body.strip(),
                       "explanation": r"Use the affine logarithmic probability formula in the entropy sum. Distributing the sum separates the weighted logarithmic ranks and the constant $\log H_{N,s}$. The proved normalization makes the total probability multiplying that constant equal to one. Writing the remaining weighted sum with its common denominator gives the stated formula."})

    ratio = (ROOT / "Solutions/Sol_ZipfLaw_zipfPMF_ratio.lean").read_text(encoding="utf-8")
    ratio_body = ratio.split("theorem solution", 1)[1].split(" := by", 1)[1].split("#print axioms", 1)[0]
    ratio_body = ratio_body.replace("zipf_harmonic_pos", "genHarmonic_pos").replace(" <;> ring", "")
    reductions.append({"name": "zipfPMF_ratio", "dependencies": ["genHarmonic_pos"],
                       "body": ratio_body.strip(),
                       "explanation": r"The generalized harmonic sum is positive, so the common normalizing denominator can be cancelled. The supported rank-one weight is one, while the rank-$n$ weight is $n^{-s}$. Their probability ratio is therefore $n^s$."})

    reductions.append({
        "name": "log_zipfPMF_affine",
        "dependencies": ["zipfPMF_ratio", "genHarmonic_pos"],
        "body": "  have hN : 1 ≤ N := le_trans hk1 hkN\n  have hH := genHarmonic_pos N hN s\n  have hkpos : 0 < (k : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk1)\n  have hpk : 0 < zipfPMF N s k := by\n    rw [zipfPMF, if_pos ⟨hk1, hkN⟩]\n    positivity\n  have hp1 : 0 < zipfPMF N s 1 := by\n    rw [zipfPMF, if_pos ⟨le_rfl, hN⟩]\n    positivity\n  have hlog := congrArg Real.log (zipfPMF_ratio N s k hk1 hkN)\n  rw [Real.log_div hp1.ne' hpk.ne', Real.log_rpow hkpos] at hlog\n  have hlog1 : Real.log (zipfPMF N s 1) = -Real.log (genHarmonic N s) := by\n    simp [zipfPMF, hN, Real.log_div (by norm_num : (1 : ℝ) ≠ 0) hH.ne']\n  rw [hlog1] at hlog\n  linarith",
        "explanation": r"For supported rank $k$, both probabilities are positive. Take logarithms in the rank-frequency ratio $f(1)/f(k)=k^s$, obtaining $\log f(1)-\log f(k)=s\log k$. Since $f(1)=1/H_{N,s}$, its logarithm is $-\log H_{N,s}$. Solving for $\log f(k)$ gives the affine law.",
    })
    reductions.append({
        "name": "zipfPMF_mode",
        "dependencies": ["zipfPMF_ratio", "genHarmonic_pos"],
        "body": "  have hH := genHarmonic_pos N hN s\n  have h1 : zipfPMF N s 1 = 1 / genHarmonic N s := by simp [zipfPMF, hN]\n  by_cases hk : 1 ≤ k ∧ k ≤ N\n  · have hpk : 0 < zipfPMF N s k := by\n      rw [zipfPMF, if_pos hk]\n      have hkpos : 0 < (k : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk.1)\n      positivity\n    have hratio : 1 ≤ zipfPMF N s 1 / zipfPMF N s k := by\n      rw [zipfPMF_ratio N s k hk.1 hk.2]\n      exact Real.one_le_rpow (by exact_mod_cast hk.1) hs\n    simpa using (le_div_iff₀ hpk).mp hratio\n  · rw [zipfPMF, if_neg hk, h1]\n    positivity",
        "explanation": r"For a supported rank $k\ge1$ and nonnegative exponent $s$, the rank-frequency formula gives $f(1)/f(k)=k^s\ge1$. Positivity of $f(k)$ then yields $f(k)\le f(1)$. Outside the support the probability is zero, while the rank-one probability is nonnegative.",
    })

    for item in helpers + reductions:
        name = item["name"]
        sig = item.get("signature") or signature(name)
        imports = "".join(f"import Theorems.Thm_ZipfLaw_{dep}\n" for dep in item["dependencies"])
        prefix = item.get("prefix", "")
        body = item["body"]
        if body and not body.startswith("  "):
            body = "  " + body
        code = imports + BASE + prefix + f"theorem solution {sig} := by\n{body}\n\n#print axioms solution\n"
        item["source"] = f"missions/zipf/graph/solutions/{name}.lean"
        write(ROOT / item["source"], code)
        item["explanation_file"] = f"missions/zipf/graph/explanations/{name}.md"
        write(ROOT / item["explanation_file"], item["explanation"])
        if item in helpers:
            item["formal_statement"] = f"namespace ZipfLaw\n\ntheorem {name} {sig} := by sorry\n\nend ZipfLaw"
            item["problem"] = {"theorem_name": f"ZipfLaw.{name}", "theorem_title": item["title"],
                               "formal_statement": item["formal_statement"],
                               "natural_language_statement": item["statement"],
                               "preamble": "import Mathlib\nimport Definitions.Def_ZipfLaw_Defs",
                               "source": SOURCE, "tags": ["zipf-law", "harmonic-numbers", "power-law"]}
    for item in helpers + reductions:
        for field in ("prefix", "body", "signature", "explanation"):
            item.pop(field, None)
    plan = {"env": ENV, "helpers": helpers, "reductions": reductions,
            "independent_roots": ["zipfMandelbrotPMF_hasSum_one", "yuleSimon_tail", "monkey_typing_power_law", "zipf_one_leadingDigit_benford"]}
    write(GRAPH / "plan.json", json.dumps(plan, ensure_ascii=False, indent=2))
    print(f"Prepared {len(helpers)} helper declarations and {len(reductions)} genuine reductions.")


if __name__ == "__main__":
    main()
