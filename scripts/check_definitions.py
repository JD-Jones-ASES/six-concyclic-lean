#!/usr/bin/env python3
"""Check that the ten definitions of Challenge.lean and SixConcyclic/Defs.lean agree character for
character with each other and with OpenAI's lean/ComparatorChallenges/EuclideanRamsey.lean at commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a, up to the namespace line. The reference file is read from
the path given as the first argument (default: scripts/EuclideanRamsey.oai.lean) and is not part of
the development. Exit status 0 means every definition block agrees."""

from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
NAMES = ["Space", "Congruent", "Ramsey", "coordinateField", "Coeff", "TensorRing", "coordinate",
         "augmented", "multiply", "FieldCriterion"]


def blocks(text):
    """The definition blocks, keyed by name: from the `abbrev`/`def` line to the blank line after it."""
    out = {}
    lines = text.splitlines()
    for idx, line in enumerate(lines):
        m = re.match(r"^(abbrev|def) (\w+)", line)
        if m and m.group(2) in NAMES:
            end = idx
            while end + 1 < len(lines) and lines[end + 1].strip() != "":
                end += 1
            out[m.group(2)] = "\n".join(lines[idx:end + 1])
    return out


def main():
    ref_path = Path(sys.argv[1]) if len(sys.argv) > 1 else ROOT / "scripts" / "EuclideanRamsey.oai.lean"
    ref = blocks(ref_path.read_text(encoding="utf-8"))
    ok = True
    for rel in ("Challenge.lean", "SixConcyclic/Defs.lean"):
        ours = blocks((ROOT / rel).read_text(encoding="utf-8"))
        for name in NAMES:
            if name not in ref:
                print(f"reference lacks {name}")
                ok = False
                continue
            if name not in ours:
                print(f"{rel} lacks {name}")
                ok = False
                continue
            if ours[name] != ref[name]:
                print(f"{rel}: {name} differs from the reference")
                print("  ours:", ours[name].replace("\n", "\n        "))
                print("  ref: ", ref[name].replace("\n", "\n        "))
                ok = False
            else:
                print(f"ok    {rel}: {name}")
    print("ALL DEFINITIONS AGREE" if ok else "DEFINITIONS DIFFER")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
