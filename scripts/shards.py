#!/usr/bin/env python3
"""Plan the continuous-integration build of this repository, and audit it.

The proof is far larger than one GitHub-hosted job -- roughly a hundred
CPU-hours -- so `.github/workflows/verify.yml` builds it as a matrix.  This
script is the single source of truth for that matrix: it reads the import
graph, splits it into strata that mirror the structure of the proof, and
hands each job the list of modules it is responsible for.

    python3 scripts/shards.py matrix                # the CI matrix, as JSON
    python3 scripts/shards.py targets subtree 3 20  # one job's module list
    python3 scripts/shards.py targets final         # what the last job builds
    python3 scripts/shards.py build subtree 3 20    # dependency-safe CI build
    python3 scripts/shards.py audit                 # closure report
"""
from __future__ import annotations

import concurrent.futures
import functools
import json
import os
import re
import subprocess
import sys
from pathlib import Path
from typing import Callable

ROOT = Path(__file__).resolve().parents[1]
FINAL_MODULE = "SRG266.FractionalNearFrameMain"

# How many CI jobs each stratum is split across.  Every stratum has a small
# shared base -- 72 modules for `subtree`, about 500 for `a15` and `ade` --
# so a job's cost is dominated by its own targets, and the counts below keep
# every job near three hours against GitHub's six-hour limit.  There are more
# jobs here than the twenty a free account runs at once; the surplus queues.
SHARDS = {
    "subtree": 20,  # 1,226 residual certificate chains, about four minutes each
    "a15": 3,       #   731 A15 enumeration chunks, about fifty seconds each
    "ade": 1,       #   690 ADE root-orbit certificates
    "orbit": 1,     # 1,588 rooted near-orbit data modules and LRAT replays
    "cubic": 1,     #   556 rooted-cubic prefix certificates
    "data": 3,      # 1,102 remaining certificate modules: centroids, projectors,
                    #       PSD rows, support kernels, and the dispatcher entries
}

# The four modules that assemble the headline theorem.
ASSEMBLY = (
    "SRG266.Certificates.FractionalNearFrame.All",
    "SRG266.Certificates.FractionalNearFrame.Closed",
    "SRG266.Certificates.FractionalNearFrame.Final",
    "SRG266.FractionalNearFrameMain",
)

# The certificate families.  Each is a stratum of its own, because each has
# its own shared base and its own per-module cost.
FAMILIES = ("subtree", "a15", "ade", "orbit", "cubic")

# Anything that would make the build depend on something other than the Lean
# kernel: compiled evaluation, floating point, or an admitted goal.
BANNED = {
    "native_decide": re.compile(r"\bnative_decide\b"),
    "ofReduceBool": re.compile(r"\bofReduceBool\b"),
    "sorry": re.compile(r"\bsorry\b"),
    "Float": re.compile(r"\bFloat\b"),
    "implemented_by": re.compile(r"@\[implemented_by"),
    "extern": re.compile(r"@\[extern"),
}

IMPORT_RE = re.compile(r"^import\s+([A-Za-z0-9_.]+)", re.M)
INCLUDE_STR_RE = re.compile(r'\binclude_str\s+"([^"\n]+)"')
BLOCK_COMMENT_RE = re.compile(r"/-.*?-/", re.S)
LINE_COMMENT_RE = re.compile(r"--[^\n]*")


def source(module: str) -> Path:
    path = ROOT / (module.replace(".", "/") + ".lean")
    if not path.exists():
        raise SystemExit(f"missing module source: {module}")
    return path


@functools.cache
def imports_of(module: str) -> tuple[str, ...]:
    return tuple(m for m in IMPORT_RE.findall(source(module).read_text())
                 if m.startswith("SRG266"))


@functools.cache
def closure(module: str = FINAL_MODULE) -> frozenset[str]:
    """Every SRG266 module this one transitively imports, itself included."""
    seen = {module}
    for dependency in imports_of(module):
        seen |= closure(dependency)
    return frozenset(seen)


@functools.cache
def module_index() -> dict[str, int]:
    """A stable bit position for every module in the headline closure."""
    return {module: index for index, module in enumerate(sorted(closure()))}


@functools.cache
def closure_mask(module: str) -> int:
    """The SRG266 import closure as a compact bit set.

    The scheduler performs thousands of overlap checks.  Python integer bit
    operations make those checks effectively constant-time, whereas repeatedly
    subtracting sets of module-name strings adds minutes of planner overhead.
    """
    mask = 1 << module_index()[module]
    for dependency in imports_of(module):
        mask |= closure_mask(dependency)
    return mask


def family_of(module: str) -> str:
    """Which certificate family a module belongs to, by name alone."""
    if module.startswith(ASSEMBLY):
        return "final"
    if module.endswith(("Kernel", "KernelRule")) or "KernelHall" in module:
        return "final"
    if "FractionalNearFrameSubtree" in module:
        return "subtree"
    if "A15EnumerationChunks" in module:
        return "a15"
    if "ADERootOrbits" in module:
        return "ade"
    if "RootNearOrbit" in module:
        return "orbit"
    if "RootCubic" in module:
        return "cubic"
    return "core"


@functools.cache
def stratum_of(module: str) -> str:
    """Which CI job builds a module.

    The certificate families shard cleanly, because their members are leaves
    over a small shared base.  What does not shard is everything above them:
    the aggregator that gathers a whole directory of certificates, and the
    spine of lattice and design theory that stands on those aggregators.
    Every module up there transitively needs most of the proof, so no build
    job can produce it and splitting them apart saves nothing.  They go to
    the final job, which elaborates them from the merged oleans instead of
    rebuilding anything.
    """
    family = family_of(module)
    if family != "core":
        return family
    if {family_of(m) for m in closure(module)} & set(FAMILIES):
        return "final"
    part = module.split(".")
    if len(part) >= 4 and part[1] == "Certificates":
        return "data"
    return "final"


def targets(stratum: str, shard: int = 0, of: int = 1) -> list[str]:
    # By closure size, which is a topological order: if one module imports
    # another its closure is strictly larger.  The final job elaborates its
    # list in sequence and so needs that, and nothing else is harmed by it.
    picked = sorted((m for m in closure() if stratum_of(m) == stratum),
                    key=lambda m: (len(closure(m)), m))
    if stratum == "subtree":
        # One target per representative: building `<rep>P` pulls its own
        # D/S/T chain, so the list stays short and the order stays stable.
        picked = [m for m in picked if m.endswith("P")]
    # Round-robin, not contiguous blocks: neighbouring names are the same
    # kind of certificate, and those are not equally expensive.
    return picked[shard::of]


def run_lake(target: str) -> int:
    """Build one target, inheriting the job's stdout, stderr and environment."""
    return subprocess.run(["lake", "build", target], check=False).returncode


def build_shard(stratum: str, shard: int, of: int, parallel: int,
                runner: Callable[[str], int] = run_lake) -> int:
    """Build a shard without concurrent writes to shared dependencies.

    A successful `lake build M` has built the whole Lean import closure of `M`.
    While it is running, no other target whose still-unbuilt closure overlaps
    that closure may start.  Once it completes, those dependencies become
    read-only inputs and independent targets can run alongside one another.

    This retains two-way parallelism for the expensive independent certificate
    leaves, but builds each shared base only once.  It also skips a listed
    target if an earlier target already built it as a dependency.
    """
    if parallel < 1:
        raise SystemExit(f"PARALLEL must be positive, got {parallel}")
    goals = targets(stratum, shard, of)
    pending = goals.copy()
    total = len(goals)
    built = 0
    started = 0
    skipped = 0

    print(f"{total} targets; dependency-safe parallelism {parallel}", flush=True)
    with concurrent.futures.ThreadPoolExecutor(max_workers=parallel) as pool:
        running: dict[concurrent.futures.Future[int],
                      tuple[str, int]] = {}
        while pending or running:
            # Importers can make a module listed later in the plan redundant.
            still_pending: list[str] = []
            for target in pending:
                if built & (1 << module_index()[target]):
                    skipped += 1
                else:
                    still_pending.append(target)
            pending = still_pending

            claimed = 0
            for _, remaining in running.values():
                claimed |= remaining
            while pending and len(running) < parallel:
                choice = None
                for index, target in enumerate(pending):
                    remaining = closure_mask(target) & ~built
                    if not (remaining & claimed):
                        choice = (index, target, remaining)
                        break
                if choice is None:
                    break
                index, target, remaining = choice
                pending.pop(index)
                claimed |= remaining
                started += 1
                print(f"[{started}/{total}] start {target}", flush=True)
                future = pool.submit(runner, target)
                running[future] = (target, remaining)

            if not running:
                raise RuntimeError("scheduler deadlock with pending targets")

            done, _ = concurrent.futures.wait(
                running, return_when=concurrent.futures.FIRST_COMPLETED)
            failures: list[str] = []
            for future in done:
                target, _ = running.pop(future)
                if future.result() == 0:
                    built |= closure_mask(target)
                    print(f"done {target}", flush=True)
                else:
                    failures.append(target)

            if failures:
                # Stop scheduling, let disjoint in-flight work finish, then
                # retry failures without any concurrent Lake process.  A
                # repeated failure remains a genuine CI failure.
                for future, (target, _) in list(running.items()):
                    if future.result() == 0:
                        built |= closure_mask(target)
                        print(f"done {target}", flush=True)
                    else:
                        failures.append(target)
                running.clear()
                for target in failures:
                    print(f"::warning::Retrying {target} serially", flush=True)
                    if runner(target) != 0:
                        return 1
                    built |= closure_mask(target)
                    print(f"done {target} (serial retry)", flush=True)

    required = 0
    for target in goals:
        required |= closure_mask(target)
    if required & ~built:
        raise RuntimeError(
            "scheduler completed without building the whole shard closure")
    print(f"built {started} targets; skipped {skipped} already-built targets",
          flush=True)
    return 0


def strip_comments(text: str) -> str:
    """Drop prose, so the banned-construct scan only sees code.

    Modules document themselves with sentences like "no `native_decide`",
    which is exactly the string the scan looks for.
    """
    return LINE_COMMENT_RE.sub("", BLOCK_COMMENT_RE.sub("", text))


def audit() -> int:
    modules = closure()
    print(f"closure of {FINAL_MODULE}: {len(modules)} modules")
    counts: dict[str, int] = {}
    for module in modules:
        counts[stratum_of(module)] = counts.get(stratum_of(module), 0) + 1
    for stratum, count in sorted(counts.items()):
        print(f"  {stratum:8s} {count}")
    offenders: dict[str, list[str]] = {}
    missing_includes: list[tuple[str, str]] = []
    for module in sorted(modules):
        module_source = source(module)
        code = strip_comments(module_source.read_text())
        for name, pattern in BANNED.items():
            if pattern.search(code):
                offenders.setdefault(name, []).append(module)
        for relative in INCLUDE_STR_RE.findall(code):
            included = (module_source.parent / relative).resolve()
            try:
                included.relative_to(ROOT.resolve())
            except ValueError:
                missing_includes.append((module, relative))
                continue
            if not included.is_file():
                missing_includes.append((module, relative))
    if not offenders and not missing_includes:
        print("no native_decide, ofReduceBool, sorry, Float, "
              "@[implemented_by] or @[extern] in the closure")
        print("all include_str inputs are present inside the repository")
        return 0
    for name, hits in sorted(offenders.items()):
        print(f"{name}: {len(hits)} modules")
        for module in hits[:10]:
            print(f"    {module}")
    if missing_includes:
        print(f"missing or external include_str inputs: {len(missing_includes)}")
        for module, relative in missing_includes[:10]:
            print(f"    {module}: {relative}")
    return 1


def main(argv: list[str]) -> int:
    sys.setrecursionlimit(10000)
    if len(argv) < 2:
        print(__doc__, file=sys.stderr)
        return 2
    command = argv[1]
    if command == "matrix":
        print(json.dumps([{"stratum": s, "shard": i, "of": n}
                          for s, n in SHARDS.items() for i in range(n)]))
        return 0
    if command == "targets" and len(argv) >= 3:
        shard = int(argv[3]) if len(argv) > 3 else 0
        of = int(argv[4]) if len(argv) > 4 else 1
        print("\n".join(targets(argv[2], shard, of)))
        return 0
    if command == "build" and len(argv) >= 3:
        shard = int(argv[3]) if len(argv) > 3 else 0
        of = int(argv[4]) if len(argv) > 4 else 1
        parallel = int(os.environ.get("PARALLEL", "2"))
        return build_shard(argv[2], shard, of, parallel)
    if command == "audit":
        return audit()
    print(__doc__, file=sys.stderr)
    return 2


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
