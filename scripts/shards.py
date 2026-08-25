#!/usr/bin/env python3
"""Plan the continuous-integration build of this repository, and audit it.

The proof is far larger than one GitHub-hosted job -- roughly a hundred
CPU-hours -- so `.github/workflows/verify.yml` builds it as a matrix.  This
script is the single source of truth for that matrix: it reads the import
graph, splits it into strata that mirror the structure of the proof, and
hands each job the list of modules it is responsible for.

    python3 scripts/shards.py matrix base           # the twenty base jobs
    python3 scripts/shards.py matrix fanout         # the post-merge fan-out
    python3 scripts/shards.py targets base 3        # one base job's targets
    python3 scripts/shards.py targets fanout hall 2 # one fan-out job
    python3 scripts/shards.py targets tail          # final dependent tail
    python3 scripts/shards.py build-base 3          # dependency-safe Lake build
    python3 scripts/shards.py build-direct fanout hall 2
    python3 scripts/shards.py build-direct tail
    python3 scripts/shards.py count pretail         # expected artifact count
    python3 scripts/shards.py audit                 # closure and pipeline report
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
from typing import Callable, Iterable

ROOT = Path(__file__).resolve().parents[1]
FINAL_MODULE = "SRG266.FractionalNearFrameMain"

# The fine-grained slices from which the first CI stage is assembled.  Keeping
# these stable makes the split reproducible; BASE_JOBS below packs the slices
# into exactly twenty runners using timings from the v1.0 verification run.
SHARDS = {
    "subtree": 20,  # 1,226 residual certificate chains, about four minutes each
    "a15": 3,       #   731 A15 enumeration chunks, about fifty seconds each
    "ade": 1,       #   690 ADE root-orbit certificates
    "orbit": 1,     # 1,588 rooted near-orbit data modules and LRAT replays
    "cubic": 1,     #   556 rooted-cubic prefix certificates
    "data": 3,      # 1,102 remaining certificate modules: centroids, projectors,
                    #       PSD rows, support kernels, and the dispatcher entries
}

# GitHub runs twenty jobs concurrently for this repository.  The old matrix
# exposed all twenty-nine slices as jobs, leaving nine queued.  In particular,
# the 116-minute ADE slice started 75 minutes late and became the critical
# path.  These bins put every slice in the first wave and pair the shorter
# subtree slices.  A pair also shares its 72-module base within one runner.
BASE_JOBS = (
    (("subtree", 3), ("subtree", 0)),
    (("subtree", 11), ("subtree", 7)),
    (("subtree", 15), ("subtree", 13)),
    (("subtree", 9), ("subtree", 1)),
    (("subtree", 2), ("subtree", 17)),
    (("subtree", 10), ("subtree", 5)),
    (("subtree", 4), ("subtree", 14)),
    (("subtree", 18), ("subtree", 19)),
    (("a15", 2),),
    (("a15", 1),),
    (("a15", 0),),
    (("subtree", 16), ("cubic", 0)),
    (("ade", 0),),
    (("data", 2),),
    (("orbit", 0),),
    (("data", 1),),
    (("data", 0),),
    (("subtree", 8),),
    (("subtree", 6),),
    (("subtree", 12),),
)

# The expensive Hall dispatchers are mutually independent once the base
# artifacts have been merged.  Source size is a useful stable approximation
# to their cost; ten greedy bins held the longest bin below nine minutes when
# replayed against the successful v1.0 CI timings.
HALL_SHARDS = 10

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


def base_targets(job: int) -> list[str]:
    """The goals assigned to one of the twenty first-stage runners."""
    if not 0 <= job < len(BASE_JOBS):
        raise SystemExit(f"base job must be in [0, {len(BASE_JOBS)}), got {job}")
    picked: set[str] = set()
    for stratum, shard in BASE_JOBS[job]:
        picked.update(targets(stratum, shard, SHARDS[stratum]))
    return sorted(picked, key=lambda m: (len(closure(m)), m))


@functools.cache
def base_modules() -> frozenset[str]:
    """Every module produced, as a goal or dependency, by the base matrix."""
    built: set[str] = set()
    for job in range(len(BASE_JOBS)):
        for module in base_targets(job):
            built.update(closure(module))
    return frozenset(built)


@functools.cache
def hall_modules() -> tuple[str, ...]:
    """Expensive mutually independent dispatchers missing after the base."""
    return tuple(sorted(
        (m for m in closure() - base_modules() if "KernelHall" in m),
        key=lambda m: (len(closure(m)), m),
    ))


@functools.cache
def tail_modules() -> tuple[str, ...]:
    """The small final spine whose closure uses at least one Hall dispatcher."""
    hall = set(hall_modules())
    missing = closure() - base_modules() - hall
    return tuple(sorted(
        (m for m in missing if not closure(m).isdisjoint(hall)),
        key=lambda m: (len(closure(m)), m),
    ))


@functools.cache
def side_modules() -> tuple[str, ...]:
    """Post-base modules that can build alongside, rather than after, Hall."""
    picked = (closure() - base_modules()
              - set(hall_modules()) - set(tail_modules()))
    return tuple(sorted(picked, key=lambda m: (len(closure(m)), m)))


@functools.cache
def hall_bins() -> tuple[tuple[str, ...], ...]:
    """Greedily balance Hall modules by source size."""
    bins: list[list[str]] = [[] for _ in range(HALL_SHARDS)]
    weights = [0] * HALL_SHARDS
    by_size = sorted(hall_modules(),
                     key=lambda m: (source(m).stat().st_size, m),
                     reverse=True)
    for module in by_size:
        shard = min(range(HALL_SHARDS), key=lambda i: (weights[i], i))
        bins[shard].append(module)
        weights[shard] += source(module).stat().st_size
    return tuple(tuple(sorted(group, key=lambda m: (len(closure(m)), m)))
                 for group in bins)


def base_matrix() -> list[dict[str, object]]:
    matrix: list[dict[str, object]] = []
    for job, units in enumerate(BASE_JOBS):
        label = "+".join(f"{stratum}-{shard}" for stratum, shard in units)
        matrix.append({"job": job, "label": label})
    return matrix


def fanout_matrix() -> list[dict[str, object]]:
    matrix = [
        {"kind": "hall", "shard": shard, "label": f"hall-{shard}"}
        for shard in range(HALL_SHARDS)
    ]
    matrix.append({"kind": "side", "shard": 0, "label": "side"})
    return matrix


def fanout_targets(kind: str, shard: int) -> list[str]:
    if kind == "hall":
        if not 0 <= shard < HALL_SHARDS:
            raise SystemExit(
                f"Hall shard must be in [0, {HALL_SHARDS}), got {shard}")
        return list(hall_bins()[shard])
    if kind == "side" and shard == 0:
        return list(side_modules())
    raise SystemExit(f"unknown fan-out target {kind} {shard}")


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


def build_base(job: int, parallel: int,
               runner: Callable[[str], int] = run_lake) -> int:
    """Build every fine-grained slice packed into one base runner."""
    if not 0 <= job < len(BASE_JOBS):
        raise SystemExit(f"base job must be in [0, {len(BASE_JOBS)}), got {job}")
    for stratum, shard in BASE_JOBS[job]:
        print(f"::group::{stratum} slice {shard}/{SHARDS[stratum]}",
              flush=True)
        result = build_shard(stratum, shard, SHARDS[stratum], parallel,
                             runner=runner)
        print("::endgroup::", flush=True)
        if result != 0:
            return result
    return 0


def olean_path(root: Path, module: str) -> Path:
    return root / (module.replace(".", "/") + ".olean")


def run_lean(module: str, output_root: Path) -> int:
    """Elaborate one source module directly into a stage-local olean tree."""
    output = olean_path(output_root, module)
    output.parent.mkdir(parents=True, exist_ok=True)
    relative_source = source(module).relative_to(ROOT)
    return subprocess.run(
        ["lean", str(relative_source), "-o", str(output)],
        cwd=ROOT,
        check=False,
    ).returncode


def build_direct(modules: Iterable[str], output_root: Path, parallel: int,
                 runner: Callable[[str, Path], int] = run_lean) -> int:
    """Elaborate a stage in import order without asking Lake for C outputs.

    Every import outside `modules` must already be on LEAN_PATH.  Modules in
    this stage become ready as soon as their same-stage imports have finished.
    This lets the ordinary side branches use two Lean processes while the
    memory-heavy Hall jobs request one.
    """
    if parallel < 1:
        raise SystemExit(f"parallelism must be positive, got {parallel}")
    requested = tuple(modules)
    pending = set(requested)
    if len(pending) != len(requested):
        raise RuntimeError("direct-build target list contains duplicates")
    total = len(pending)
    started = 0
    completed = 0
    running: dict[concurrent.futures.Future[int], str] = {}
    print(f"{total} direct targets; parallelism {parallel}", flush=True)

    with concurrent.futures.ThreadPoolExecutor(max_workers=parallel) as pool:
        while pending or running:
            unbuilt = pending | set(running.values())
            ready = sorted(
                (m for m in pending if set(imports_of(m)).isdisjoint(unbuilt)),
                key=lambda m: (len(closure(m)), m),
            )
            while ready and len(running) < parallel:
                module = ready.pop(0)
                pending.remove(module)
                started += 1
                print(f"[{started}/{total}] start {module}", flush=True)
                running[pool.submit(runner, module, output_root)] = module

            if not running:
                blocked = ", ".join(sorted(pending)[:5])
                raise RuntimeError(
                    f"direct-build dependency deadlock near {blocked}")

            done, _ = concurrent.futures.wait(
                running, return_when=concurrent.futures.FIRST_COMPLETED)
            failures: list[str] = []
            for future in done:
                module = running.pop(future)
                if future.result() == 0:
                    completed += 1
                    print(f"done {module}", flush=True)
                else:
                    failures.append(module)
            if failures:
                for future, module in list(running.items()):
                    if future.result() != 0:
                        failures.append(module)
                print("direct build failed: " + ", ".join(failures),
                      file=sys.stderr, flush=True)
                return 1

    missing_outputs = [m for m in requested
                       if not olean_path(output_root, m).is_file()]
    if missing_outputs:
        raise RuntimeError(
            f"direct build produced no olean for {missing_outputs[:5]}")
    print(f"built {completed} direct targets", flush=True)
    return 0


def strip_comments(text: str) -> str:
    """Drop prose, so the banned-construct scan only sees code.

    Modules document themselves with sentences like "no `native_decide`",
    which is exactly the string the scan looks for.
    """
    return LINE_COMMENT_RE.sub("", BLOCK_COMMENT_RE.sub("", text))


def pipeline_errors() -> list[str]:
    """Check that the staged artifact graph is a partition and is runnable."""
    errors: list[str] = []
    expected_units = {(stratum, shard)
                      for stratum, count in SHARDS.items()
                      for shard in range(count)}
    actual_units = [unit for job in BASE_JOBS for unit in job]
    if len(actual_units) != len(set(actual_units)):
        errors.append("a fine-grained base slice occurs in more than one job")
    if set(actual_units) != expected_units:
        missing = sorted(expected_units - set(actual_units))
        extra = sorted(set(actual_units) - expected_units)
        errors.append(f"base bins mismatch: missing={missing}, extra={extra}")
    if len(BASE_JOBS) != 20:
        errors.append(f"expected 20 base jobs, found {len(BASE_JOBS)}")

    base = set(base_modules())
    hall = set(hall_modules())
    side = set(side_modules())
    tail = set(tail_modules())
    stages = (base, hall, side, tail)
    names = ("base", "hall", "side", "tail")
    for i, left in enumerate(stages):
        for j, right in enumerate(stages[i + 1:], start=i + 1):
            overlap = left & right
            if overlap:
                errors.append(
                    f"{names[i]}/{names[j]} overlap at {sorted(overlap)[:5]}")
    covered = set().union(*stages)
    if covered != set(closure()):
        errors.append(
            f"pipeline coverage mismatch: missing "
            f"{sorted(set(closure()) - covered)[:5]}, extra "
            f"{sorted(covered - set(closure()))[:5]}")

    hall_binned = [m for group in hall_bins() for m in group]
    if len(hall_binned) != len(set(hall_binned)) or set(hall_binned) != hall:
        errors.append("Hall bins do not partition the Hall modules")

    # A direct-build job can import its own earlier modules and anything from
    # an earlier artifact stage, but must not wait for a sibling matrix job.
    for module in hall:
        unavailable = set(imports_of(module)) - base
        if unavailable:
            errors.append(
                f"Hall module {module} has non-base imports {sorted(unavailable)}")
    side_available = base | side
    for module in side:
        unavailable = set(imports_of(module)) - side_available
        if unavailable:
            errors.append(
                f"side module {module} has unavailable imports "
                f"{sorted(unavailable)}")
    tail_available = base | hall | side | tail
    for module in tail:
        unavailable = set(imports_of(module)) - tail_available
        if unavailable:
            errors.append(
                f"tail module {module} has unavailable imports "
                f"{sorted(unavailable)}")
    return errors


def audit() -> int:
    modules = closure()
    print(f"closure of {FINAL_MODULE}: {len(modules)} modules")
    counts: dict[str, int] = {}
    for module in modules:
        counts[stratum_of(module)] = counts.get(stratum_of(module), 0) + 1
    for stratum, count in sorted(counts.items()):
        print(f"  {stratum:8s} {count}")
    print("artifact pipeline:")
    print(f"  base     {len(base_modules()):5d} modules in "
          f"{len(BASE_JOBS)} jobs")
    print(f"  hall     {len(hall_modules()):5d} modules in "
          f"{HALL_SHARDS} jobs")
    print(f"  side     {len(side_modules()):5d} modules in 1 job")
    print(f"  tail     {len(tail_modules()):5d} modules in final job")
    pipeline_problems = pipeline_errors()
    if pipeline_problems:
        print("pipeline errors:")
        for problem in pipeline_problems:
            print(f"    {problem}")
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
    if not offenders and not missing_includes and not pipeline_problems:
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
    if command == "matrix" and len(argv) == 3:
        if argv[2] == "base":
            print(json.dumps(base_matrix()))
            return 0
        if argv[2] == "fanout":
            print(json.dumps(fanout_matrix()))
            return 0
    if command == "count" and len(argv) == 3:
        counts = {
            "base": len(base_modules()),
            "pretail": (len(base_modules()) + len(hall_modules())
                        + len(side_modules())),
            "total": len(closure()),
        }
        if argv[2] in counts:
            print(counts[argv[2]])
            return 0
    if command == "targets" and len(argv) >= 3:
        if argv[2] == "base" and len(argv) == 4:
            print("\n".join(base_targets(int(argv[3]))))
            return 0
        if argv[2] == "fanout" and len(argv) == 5:
            print("\n".join(fanout_targets(argv[3], int(argv[4]))))
            return 0
        if argv[2] == "tail" and len(argv) == 3:
            print("\n".join(tail_modules()))
            return 0
    if command == "build-base" and len(argv) == 3:
        parallel = int(os.environ.get("PARALLEL", "2"))
        return build_base(int(argv[2]), parallel)
    if command == "build-direct":
        output_root = ROOT / os.environ.get(
            "OLEAN_OUT", ".lake/build/lib/lean")
        if len(argv) == 5 and argv[2] == "fanout":
            kind = argv[3]
            parallel = (1 if kind == "hall"
                        else int(os.environ.get("PARALLEL", "2")))
            return build_direct(
                fanout_targets(kind, int(argv[4])), output_root, parallel)
        if len(argv) == 3 and argv[2] == "tail":
            return build_direct(tail_modules(), output_root, 1)
    # Retain the fine-grained commands for local diagnosis of one slice.
    if command == "targets-slice" and len(argv) >= 3:
        shard = int(argv[3]) if len(argv) > 3 else 0
        of = int(argv[4]) if len(argv) > 4 else 1
        print("\n".join(targets(argv[2], shard, of)))
        return 0
    if command == "build-slice" and len(argv) >= 3:
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
