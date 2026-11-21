"""Compile the local balanced-quorum proof dependencies with the pinned Lake."""

import argparse
from pathlib import Path
import re
import subprocess


def build(roots: list[str]) -> None:
    formal = Path(__file__).resolve().parent
    ordered: list[str] = []
    external: set[str] = set()
    seen: set[str] = set()

    def visit(module: str) -> None:
        if module in seen:
            return
        seen.add(module)
        source = formal / (module.replace(".", "/") + ".lean")
        for imported in re.findall(r"^import\s+(\S+)", source.read_text(), re.MULTILINE):
            if (formal / (imported.replace(".", "/") + ".lean")).exists():
                visit(imported)
            elif imported.split(".", 1)[0] not in {"Init", "Lean", "Std"}:
                external.add(imported)
        ordered.append(module)

    for module in roots:
        visit(module)
    if external:
        subprocess.run(["lake", "build", *sorted(external)], cwd=formal, check=True)
    for module in ordered:
        relative = Path(module.replace(".", "/") + ".lean")
        output = Path(".lake/build/lib/lean") / relative.with_suffix(".olean")
        (formal / output).parent.mkdir(parents=True, exist_ok=True)
        subprocess.run(["lake", "env", "lean", str(relative), "-o", str(output)],
                       cwd=formal, check=True)
        print(module + ": passed", flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--roots", nargs="+", default=["MixedCircleAssembly", "MixedCircleControls"])
    build(parser.parse_args().roots)
