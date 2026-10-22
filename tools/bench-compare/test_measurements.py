import json
from pathlib import Path
import tempfile
import unittest

from measurements import parse_criterion, parse_go, positive, summarize


def go_output():
    return "\n".join(f"Benchmark{schema}/{operation}-1 100 12.5 ns/op 32 B/op 1 allocs/op"
                     for schema in ("Header", "Mixed") for operation in ("Encode", "Decode", "Root", "EncodeReuse"))


class MeasurementTests(unittest.TestCase):
    def test_should_parse_all_go_cases_and_refuse_missing_or_duplicate_results(self):
        records = parse_go(go_output())
        self.assertEqual(len(records), 8)
        self.assertEqual(records["mixed/encode_reuse/fastssz"], {"ns":12.5, "bytes":32, "allocations":1})
        for output in ("", go_output().splitlines()[0], go_output()+"\n"+go_output()):
            with self.assertRaises(ValueError): parse_go(output)

    def test_should_read_criterion_means_and_reject_incomplete_case_inventories(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            with self.assertRaises(ValueError): parse_criterion(root, "round1")
            for schema in ("header", "mixed"):
                for library in ("nyx", "libssz"):
                    for operation in ("encode", "decode", "root", "encode_reuse"):
                        if operation == "encode_reuse" and library == "nyx": continue
                        path = root / f"{schema}_{operation}_{library}" / "round1"
                        path.mkdir(parents=True)
                        (path / "benchmark.json").write_text(json.dumps({"full_id":f"{schema}/{operation}/{library}"}))
                        (path / "estimates.json").write_text(json.dumps({"mean":{"point_estimate":25}}))
            self.assertEqual(len(parse_criterion(root, "round1")), 14)

    def test_should_report_median_of_run_means_without_hiding_run_variation(self):
        rounds = [{"x":{"ns":value,"bytes":32,"allocations":1}} for value in (10,30,20)]
        report = summarize(rounds)["x"]
        self.assertEqual((report["median_ns"],report["min_ns"],report["max_ns"]),(20,10,30))
        self.assertEqual(report["runs_ns"],[10,30,20])
        self.assertEqual(report["allocations_per_op"],[1,1,1])
        for value in ([], [{}], [{"x":{"ns":1}},{}]):
            with self.assertRaises(ValueError): summarize(value)

    def test_should_refuse_nonfinite_or_nonpositive_durations(self):
        for value in (0,-1,float("nan"),float("inf")):
            with self.assertRaises(ValueError): positive(value)


if __name__ == "__main__": unittest.main()
