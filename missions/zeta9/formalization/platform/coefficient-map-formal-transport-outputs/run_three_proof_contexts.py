"""One granted lane, fresh SOURCE contexts then complete controls, serially."""
import sys
import initialize_author as p
import run_author_sources as runner


def main():
    sys.stdout.reconfigure(encoding="utf-8")
    prepared = runner.gate()
    controls = p.load(p.OUT / "author-control-preparation-v2.json")
    for tag in sys.argv[1:] or ["c", "f", "m"]:
        context = next(row for row in prepared["contexts"] if row["tag"] == tag)
        runner.run(tag, "runtime")
        for index, row in enumerate(context["math_sources"]):
            p.check([row["binding"]])
            runner.run(tag, "s" + str(index).zfill(2), row["module"], row["path"])
        context = next(row for row in controls["contexts"] if row["tag"] == tag)
        for index, row in enumerate(context["rows"]):
            p.check([row["binding"]])
            runner.run(tag, "a" + str(index).zfill(2), row["module"], row["path"])


if __name__ == "__main__":
    main()
