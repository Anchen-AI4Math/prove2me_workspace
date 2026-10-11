"""Run prepared controls serially; no API or foreign mathematical objects."""
import sys
import initialize_author as p
import run_author_sources as runner


def main():
    sys.stdout.reconfigure(encoding="utf-8")
    selected = sys.argv[1:] or ["d", "c", "f", "m"]
    plan = p.load(p.OUT / "author-control-preparation-v2.json")
    for tag in selected:
        context = next(row for row in plan["contexts"] if row["tag"] == tag)
        for i, row in enumerate(context["rows"]):
            p.check([row["binding"]])
            runner.run(tag, "a" + str(i).zfill(2), row["module"], row["path"])


if __name__ == "__main__":
    main()
