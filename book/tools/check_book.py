"""Check chapters of the book against the repository.

    python book/tools/check_book.py            # every chapter
    python book/tools/check_book.py 17 18 19   # only these chapter numbers

Checks, for each chapter:

1. every line inside a ```lean block is a whole line of some Lean file;
2. every name in backticks that looks like a Lean name exists in the Lean
   files (a miss is a problem for a name with capitals, and a warning for
   an all-lowercase name, which may be a made-up local name in a formula);
3. every relative link resolves, and every #anchor exists;
4. in the glossary, each name is defined in the file its row names.

A link to a chapter that is planned in WRITING.md but not written yet is
reported as "pending" and is not a problem.
"""
import pathlib
import re
import sys

BOOK = pathlib.Path(__file__).resolve().parent.parent
ROOT = BOOK.parent

lean_sources = [
    path.read_text(encoding="utf-8")
    for path in (ROOT / "lean").rglob("*.lean")
    if ".lake" not in path.parts
]
ALL_LEAN = "\n".join(lean_sources)
LEAN_LINES = {line.strip() for line in ALL_LEAN.split("\n")}
LEAN_WORDS = set(re.findall(r"[A-Za-z_][A-Za-z0-9_'.]*", ALL_LEAN))
LEAN_WORDS |= {part for word in LEAN_WORDS for part in word.split(".")}
PLANNED = set(re.findall(r"`(\d\d-[a-z-]+\.md)`", (BOOK / "WRITING.md").read_text(encoding="utf-8")))
NOT_LEAN = {"snake_case", "SCREAMING_SNAKE_CASE", "PascalCase", "CITATION.bib"}


def slug(heading):
    return re.sub(r"[^a-z0-9 _-]", "", heading.lower()).replace(" ", "-")


def check(chapter):
    problems, warnings, pending = [], [], []
    text = chapter.read_text(encoding="utf-8")

    for block in re.findall(r"```lean\n(.*?)```", text, flags=re.S):
        for line in block.split("\n"):
            if line.strip() and line.strip() not in LEAN_LINES:
                problems.append(("lean line not in the repository", line.strip()[:100]))

    prose = re.sub(r"```.*?```", "", text, flags=re.S)
    for name in sorted(set(re.findall(r"`([A-Za-z][A-Za-z0-9_.']*)`", prose))):
        if "_" not in name or name in NOT_LEAN or name.endswith((".md", ".lean", ".py", ".sh")):
            continue
        if name in LEAN_WORDS or name.split(".")[-1] in LEAN_WORDS:
            continue
        if name.lower() == name:
            warnings.append(("lowercase name not in Lean (fine only for a made-up local name)", name))
        else:
            problems.append(("name not in Lean", name))

    for target in re.findall(r"\]\(([^)\s]+)\)", prose):
        if re.match(r"[a-z]+:", target):
            continue
        path, _, anchor = target.partition("#")
        resolved = (chapter.parent / path).resolve() if path else chapter
        if not resolved.exists():
            if path in PLANNED:
                pending.append(path)
            else:
                problems.append(("broken link", target))
        elif anchor and resolved.suffix == ".md":
            headings = re.findall(r"^#+ (.*)$", resolved.read_text(encoding="utf-8"), flags=re.M)
            if anchor not in {slug(heading) for heading in headings}:
                problems.append(("broken anchor", target))

    if chapter.name == "glossary.md":
        rows = re.findall(r"^\| (`[^|]*) \|[^|]*\| \[`[^`]*`\]\(([^)]*)\) \|$", text, flags=re.M)
        for names, path in rows:
            source = (chapter.parent / path).read_text(encoding="utf-8")
            for name in re.findall(r"`([^`]+)`", names):
                if not re.search(r"(def|abbrev|structure|theorem)\s+" + re.escape(name) + r"\b", source):
                    problems.append(("not defined in " + pathlib.Path(path).name, name))

    if re.match(r"\d\d-", chapter.name) and not chapter.name.startswith("00-"):
        if not re.match(r"# \d+\. \S", text):
            problems.append(("first line is not '# N. Title'", text.split("\n")[0][:60]))
        last = text.rstrip("\n").split("\n")[-1]
        if not last.startswith(("Previous:", "Next:")):
            problems.append(("last line is not the navigation line", last[:60]))
    return problems, warnings, pending


def main():
    sys.stdout.reconfigure(encoding="utf-8")  # a Windows console may not be UTF-8
    wanted = {number.zfill(2) for number in sys.argv[1:]}
    chapters = [
        chapter for chapter in sorted(BOOK.glob("*.md"))
        if chapter.name != "WRITING.md" and (not wanted or chapter.name[:2] in wanted)
    ]
    if wanted and len(chapters) != len(wanted):
        print("note: found", len(chapters), "chapter files for", len(wanted), "numbers")
    total = 0
    for chapter in chapters:
        problems, warnings, pending = check(chapter)
        total += len(problems)
        for kind, detail in problems:
            print(f"PROBLEM  {chapter.name}: {kind}: {detail}")
        for kind, detail in warnings:
            print(f"warning  {chapter.name}: {kind}: {detail}")
        for path in sorted(set(pending)):
            print(f"pending  {chapter.name}: links to {path}, not written yet")
        lines = chapter.read_text(encoding="utf-8").count("\n")
        print(f"checked  {chapter.name} ({lines} lines)")
    print("problems:", total)
    sys.exit(1 if total else 0)


if __name__ == "__main__":
    main()
