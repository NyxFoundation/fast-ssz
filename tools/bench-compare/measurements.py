"""Strict parsers and median-of-run-means summaries; all durations are ns/op."""
import json
import math
from pathlib import Path
import re
import statistics

SCHEMAS = ("header", "mixed")
OPERATIONS = ("encode", "decode", "root", "encode_reuse")


def positive(value):
    number = float(value)
    if not math.isfinite(number) or number <= 0:
        raise ValueError("invalid benchmark duration")
    return number


def parse_go(output):
    pattern = re.compile(r"^Benchmark(Header|Mixed)/(EncodeReuse|Encode|Decode|Root)(?:-\d+)?\s+\d+\s+([0-9.]+) ns/op\s+(\d+) B/op\s+(\d+) allocs/op$", re.MULTILINE)
    operation = {"Encode": "encode", "Decode": "decode", "Root": "root", "EncodeReuse": "encode_reuse"}
    records = {}
    for schema, name, duration, size, count in pattern.findall(output):
        key = f"{schema.lower()}/{operation[name]}/fastssz"
        if key in records:
            raise ValueError("duplicate Go measurement")
        records[key] = {"ns": positive(duration), "bytes": int(size), "allocations": int(count)}
    expected = {f"{schema}/{op}/fastssz" for schema in SCHEMAS for op in OPERATIONS}
    if records.keys() != expected:
        raise ValueError("Go benchmark inventory is incomplete")
    return records


def parse_criterion(directory, baseline):
    expected = {f"{schema}/{op}/{library}" for schema in SCHEMAS for library in ("nyx", "libssz")
                for op in OPERATIONS if op != "encode_reuse" or library == "libssz"}
    records = {}
    for path in Path(directory).glob(f"**/{baseline}/benchmark.json"):
        name = json.loads(path.read_text())["full_id"]
        if name not in expected or name in records:
            raise ValueError("unexpected or repeated Criterion benchmark")
        estimates = json.loads(path.with_name("estimates.json").read_text())
        records[name] = {"ns": positive(estimates["mean"]["point_estimate"])}
    if records.keys() != expected:
        raise ValueError("Criterion benchmark inventory is incomplete")
    return records


def summarize(rounds):
    if not rounds or any(row.keys() != rounds[0].keys() for row in rounds):
        raise ValueError("benchmark rounds must have identical nonempty inventories")
    if not rounds[0]:
        raise ValueError("empty benchmark inventory")
    result = {}
    for key in sorted(rounds[0]):
        values = [positive(row[key]["ns"]) for row in rounds]
        result[key] = {"median_ns": statistics.median(values), "min_ns": min(values),
                       "max_ns": max(values), "runs_ns": values}
        if "allocations" in rounds[0][key]:
            result[key]["allocations_per_op"] = [row[key]["allocations"] for row in rounds]
            result[key]["bytes_per_op"] = [row[key]["bytes"] for row in rounds]
    return result
