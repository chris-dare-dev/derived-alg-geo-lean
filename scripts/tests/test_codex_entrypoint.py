from __future__ import annotations

import sys
import unittest
from pathlib import Path


SCRIPT_DIR = Path(__file__).resolve().parents[1]
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from check_codex_entrypoint import valid_frontmatter  # noqa: E402


class CodexEntrypointTest(unittest.TestCase):
    def test_complete_header(self) -> None:
        self.assertTrue(
            valid_frontmatter('---\nname: run-loop\ndescription: "Resume the loop"\n---\n# Loop\n')
        )

    def test_incomplete_or_wrong_header(self) -> None:
        invalid = (
            '---\nname: run-loop\ndescription: "Resume the loop"\n',
            "---\nname: run-loop\n---\n# Loop\n",
            "---\nname: run-loop\ndescription: \n---\n# Loop\n",
            '---\nname: run-loop\ndescription: ""\n---\n# Loop\n',
            '---\nname: run-loop\ndescription: "  "\n---\n# Loop\n',
            "---\nname: run-loop\ndescription: # only a comment\n---\n# Loop\n",
            "---\nname: run-loop\ndescription: |\n---\n# Loop\n",
            "---\nname: run-loop\ndescription: null\n---\n# Loop\n",
            "---\nname: run-loop\ndescription: [unterminated\n---\n# Loop\n",
            '---\nname: run-loop\ndescription: "unterminated\n---\n# Loop\n',
            '---\nname: run-loop\ndescription: "Resume the loop"\n---\n',
            '---\nname: other\ndescription: "Resume the loop"\n---\n# Loop\n',
            '---\nname: run-loop\nname: run-loop\ndescription: "Resume the loop"\n---\n# Loop\n',
            '---\nname: run-loop\nname: other\ndescription: "Resume the loop"\n---\n# Loop\n',
        )
        for contents in invalid:
            with self.subTest(contents=contents):
                self.assertFalse(valid_frontmatter(contents))


if __name__ == "__main__":
    unittest.main()
