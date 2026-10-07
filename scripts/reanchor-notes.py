#!/usr/bin/env -S uv run --quiet python3
"""Re-point `#L<n>` line links in docs/notes/*.md at the current declaration lines.

A link [`name`](../../Path/File.lean#L123) is rewritten to the line of
`(theorem|lemma|def|noncomputable def|structure|abbrev|instance) <last component of name>` in that file.
Unresolved names are reported and left alone (exit 1).

    scripts/reanchor-notes.py [--check] [NOTE.md ...]
"""
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
LINK = re.compile(r"\[`([^`]+)`\]\(((?:\.\./)+)([^)#]+\.lean)#L(\d+)\)")
KW = r"(?:theorem|lemma|def|noncomputable def|structure|abbrev|instance)"


def decl_line(path, name):
    short = name.split()[0].split(".")[-1]
    pat = re.compile(rf"^\s*(?:@\[[^\]]*\]\s*)?(?:private |protected )?{KW} {re.escape(short)}(?:\s|$)")
    for i, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        if pat.match(line):
            return i
    return None


def main(argv):
    check = "--check" in argv
    notes = [pathlib.Path(a) for a in argv if a != "--check"] or sorted((ROOT / "docs/notes").glob("*.md"))
    bad = changed = 0
    for note in notes:
        text = note.read_text(encoding="utf-8")

        def fix(m):
            nonlocal bad, changed
            name, up, rel, old = m.groups()
            target = (note.parent / up / rel).resolve()
            n = decl_line(target, name) if target.exists() else None
            if n is None:
                bad += 1
                print(f"{note.name}: unresolved {name} -> {rel}", file=sys.stderr)
                return m.group(0)
            if str(n) != old:
                changed += 1
            return f"[`{name}`]({up}{rel}#L{n})"

        new = LINK.sub(fix, text)
        if new != text and not check:
            note.write_text(new, encoding="utf-8")
    print(f"{'stale' if check else 'updated'} links: {changed}, unresolved: {bad}")
    return 1 if bad or (check and changed) else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
