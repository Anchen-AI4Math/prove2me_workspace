"""Run only after the proof pipeline is terminal, in the same granted lane."""
import initialize_author as p
import run_author_sources as runner


def main():
    plan = p.load(p.OUT / "author-reference-type-control-preparation-v1.json")
    for index, row in enumerate(plan["rows"]):
        p.check([row["binding"]])
        runner.run("r", "rt" + str(index), row["module"], row["path"])


if __name__ == "__main__":
    main()
