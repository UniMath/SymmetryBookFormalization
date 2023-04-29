#!/usr/bin/env python3
# Run this script:
# python3 scripts/easily_fixable_long_lines.py fileName.lagda.md
# Fix some easily fixable long lines

import sys
import utils
import re
import os
import max_line_length


def check_wrap_line_type_signature(line, i, lines):
    m = re.match(r'^((\s*)[^\s.;{}()@"]+\s+:)\s(.*)', line)
    if m:
        # Check that the next line is not indented more than this one, just to be sure
        if i+1 >= len(lines) or not re.match(rf'^{m.group(2)}\s', lines[i+1]):
            line = f'{m.group(1)}\n{m.group(2)}  {m.group(3)}'
    return line


if __name__ == '__main__':

    agda_block_start = re.compile(r'^```agda\b')
    agda_block_end = re.compile(r'^```$')

    MAX_LINE_LENGTH: int = os.environ.get('MAX_LINE_LENGTH', 80)

    for fpath in utils.get_agda_files(sys.argv[1:]):

        with open(fpath, 'r') as f:
            contents = f.read()

        is_in_agda_block = False

        lines = contents.split('\n')
        for i, line in enumerate(lines):
            if agda_block_start.match(line):
                is_in_agda_block = True
            elif agda_block_end.match(line):
                is_in_agda_block = False
            elif is_in_agda_block:
                if len(line) > MAX_LINE_LENGTH and\
                        not max_line_length.can_forgive_line(line):
                    line = check_wrap_line_type_signature(line, i, lines)
            lines[i] = line

        new_contents = '\n'.join(lines)

        if new_contents != contents:
            with open(fpath, 'w') as f:
                f.write(new_contents)

    sys.exit(0)
