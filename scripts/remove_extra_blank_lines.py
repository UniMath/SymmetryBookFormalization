#!/usr/bin/env python3
# Run this script:
# $ python3 scripts/remove_extra_blank_lines.py fileName.lagda.md

import sys
import utils
import re

if __name__ == "__main__":

    for fpath in utils.get_agda_files(sys.argv[1:]):
        with open(fpath, "r") as f:
            inputText = f.read()
        output = re.sub(r"[ \t]+$", "", inputText, flags=re.MULTILINE)
        output = re.sub(r"\n\s*\n\s*\n", "\n\n", output)
        with open(fpath, "w") as f:
            f.write(output)

    sys.exit(0)
