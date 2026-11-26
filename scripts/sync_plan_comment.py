#!/usr/bin/env python3
"""Mirror tasks/detailed_plan.md onto the plan comment of a task issue.

The local file is the single source of truth; the GitHub comment is a pure
mirror, identified by the marker on its first line.

Usage:
  sync_plan_comment.py <N>           post or replace the mirror comment
  sync_plan_comment.py <N> --check   exit 0 iff the comment matches the file

Requires the `gh` CLI, authenticated, and a git repo with a GitHub remote.
"""
import json
import pathlib
import subprocess
import sys

MARKER = "<!-- detailed-plan -->"
HERE = pathlib.Path(__file__).resolve()
PLAN = HERE.parent.parent / "tasks" / "detailed_plan.md"


def gh(args):
    r = subprocess.run(["gh", *args], capture_output=True, text=True)
    if r.returncode != 0:
        sys.exit(f"gh {' '.join(args)} failed:\n{r.stderr.strip()}")
    return r.stdout


def repo_slug():
    out = gh(["repo", "view", "--json", "owner,name",
              "--jq", '.owner.login + "/" + .name'])
    return out.strip()


def find_comment(slug, n):
    """Return (id, body) of the plan comment, or (None, None)."""
    out = gh(["api", f"repos/{slug}/issues/{n}/comments", "--paginate"])
    for c in json.loads(out):
        if c.get("body", "").lstrip().startswith(MARKER):
            return c["id"], c["body"]
    return None, None


def main():
    argv = sys.argv[1:]
    check = "--check" in argv
    argv = [a for a in argv if a != "--check"]
    if len(argv) != 1 or not argv[0].isdigit():
        sys.exit(__doc__.strip())
    n = argv[0]

    if not PLAN.exists():
        sys.exit(f"plan file not found: {PLAN}")
    body = MARKER + "\n" + PLAN.read_text()

    slug = repo_slug()
    cid, cbody = find_comment(slug, n)

    if check:
        if cbody is None:
            sys.exit(1)  # no mirror comment yet
        sys.exit(0 if cbody.strip() == body.strip() else 1)

    if cid is not None:
        gh(["api", "-X", "PATCH", f"repos/{slug}/issues/comments/{cid}",
            "-f", "body=" + body])
    else:
        gh(["issue", "comment", n, "--body", body])
    print(f"synced {PLAN.name} -> issue #{n}")


if __name__ == "__main__":
    main()
