#!/usr/bin/env python3

import csv
import importlib.util
from pathlib import Path
import sys
import tempfile
import unittest


MODULE_PATH = Path(__file__).with_name("yukon_benchmark.py")
SPEC = importlib.util.spec_from_file_location("yukon_benchmark", MODULE_PATH)
assert SPEC is not None and SPEC.loader is not None
yukon_benchmark = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = yukon_benchmark
SPEC.loader.exec_module(yukon_benchmark)


class ParseModexpCsvTests(unittest.TestCase):
    def write_csv(self, rows: list[tuple[str, int, int]]) -> Path:
        temporary = tempfile.NamedTemporaryFile(mode="w", newline="", delete=False)
        self.addCleanup(Path(temporary.name).unlink, missing_ok=True)
        with temporary:
            writer = csv.writer(temporary)
            writer.writerow(["vector", "bytes", "status", "gas", "precompile"])
            for label, gas, precompile in rows:
                writer.writerow([label, 1, "ok", gas, precompile])
        return Path(temporary.name)

    def ranked_rows(self) -> list[tuple[str, int, int]]:
        rows = [(f"generated 256-bit #{index:02}", 1_000, 100) for index in range(1, 33)]
        rows += [(f"generated RSA-1024 #{index:02}", 20_000, 2_000) for index in range(1, 11)]
        rows += [(f"generated RSA-2048 #{index:02}", 300_000, 30_000) for index in range(1, 7)]
        rows += [(f"correctness-only #{index:02}", 999_999, 500) for index in range(1, 14)]
        return rows

    def test_equal_ratios_give_each_bucket_equal_influence(self) -> None:
        score, metrics = yukon_benchmark.parse_modexp_csv(
            self.write_csv(self.ranked_rows()), 61
        )

        self.assertEqual(score, 10_000)
        self.assertEqual(metrics["scoredVectors"], 48)
        self.assertEqual(
            metrics["bucketScores"],
            {"256-bit": 10_000, "RSA-1024": 10_000, "RSA-2048": 10_000},
        )

    def test_missing_ranked_vector_is_rejected(self) -> None:
        rows = self.ranked_rows()
        rows.pop(32)
        rows.append(("extra correctness-only", 1, 500))

        with self.assertRaisesRegex(ValueError, "RSA-1024.*expected 10.*got 9"):
            yukon_benchmark.parse_modexp_csv(self.write_csv(rows), 61)


if __name__ == "__main__":
    unittest.main()
