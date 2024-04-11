"""
This script parses the Ant unit test output and identifies tests which have
failed. It then retrieves their error messages from the surefire runner log
directory. It also prints out the longest-running unit tests, for possible
action by maintainers. Finally, it detects whether any tests ran multiple
times by accident. Since the Ant JUnit target defines tests to run using an
overlapping collection of include/exclude statements matching sets of files,
it is certainly possible this could happen.

The first argument should be a path to a file containing the captured output
of the Ant unit tests. The second argument should be a path to the surefire
runner log directory.
"""

from collections import Counter
from dataclasses import dataclass
import re
import sys
import xml.etree.ElementTree as ET

@dataclass
class TestReport:
    run_count: int
    failure_count: int
    error_count: int
    skip_count: int
    runtime: float
    thread_id: int
    name: str

sequential_sample = '    [junit] Running tlc2.tool.distributed.DieHardDistributedTLCTest\n    [junit] Tests run: 1, Failures: 0, Errors: 0, Skipped: 1, Time elapsed: 0.053 sec'
sequential_pattern = re.compile(
    '\[junit\] Running (?P<test_name>[\w\.]+)$\s*'
    + '\[junit\] Tests run: (?P<run_count>\d+), '
    + 'Failures: (?P<failure_count>\d+), '
    + 'Errors: (?P<error_count>\d+), '
    + 'Skipped: (?P<skip_count>\d+), '
    + 'Time elapsed: (?P<runtime>\d+\.\d+) sec',
    flags=re.MULTILINE
)
def sequential_match_to_report(match):
    return TestReport(
        int(match.group('run_count')),
        int(match.group('failure_count')),
        int(match.group('error_count')),
        int(match.group('skip_count')),
        float(match.group('runtime')),
        1,
        match.group('test_name').strip()
    )

parallel_sample = '[junit] Tests run: 1, Failures: 0, Errors: 0, Skipped: 0, Time elapsed: 0.209 sec, Thread: 7, Class: pcal.CallGotoUnlabeledTest'
parallel_pattern = re.compile(
    '\[junit\] Tests run: (?P<run_count>\d+), '
    + 'Failures: (?P<failure_count>\d+), '
    + 'Errors: (?P<error_count>\d+), '
    + 'Skipped: (?P<skip_count>\d+), '
    + 'Time elapsed: (?P<runtime>\d+\.\d+) sec, '
    + 'Thread: (?P<thread_id>\d+), '
    + 'Class: (?P<test_name>[\w\.]+)'
)
def parallel_match_to_report(match):
    return TestReport(
        int(match.group('run_count')),
        int(match.group('failure_count')),
        int(match.group('error_count')),
        int(match.group('skip_count')),
        float(match.group('runtime')),
        int(match.group('thread_id')),
        match.group('test_name').strip()
    )

reports = []
with open(sys.argv[1], 'r') as f:
    text = f.read()
    reports += [
        parallel_match_to_report(match)
        for match in re.finditer(parallel_pattern, text)
    ]
    reports += [
        sequential_match_to_report(match)
        for match in re.finditer(sequential_pattern, text)
    ]

reports = sorted(reports, key=lambda report: report.runtime, reverse=True)
failures = [
    report.name
    for report in reports
    if report.failure_count > 0 or report.error_count > 0
]
duplicates = [
    test_name
    for test_name, run_count in Counter(report.name for report in reports).items()
    if run_count > 1
]

print(f'Test count: {len(reports)}')
print(f'Failure count: {len(failures)}')
print(f'Tests run multiple times: {len(duplicates)}')
if any(duplicates):
    for duplicate in duplicates:
        print(duplicate)

print('\nLongest-running tests:')
for i, report in enumerate(reports[slice(20)]):
    print(f'{i+1:2d} | {report.runtime:5.1f} sec | {report.name}')

def node_text(node):
    text = node.text
    return text.strip() if text is not None else None

if not any(failures):
    exit(0)

print('\nFailures:\n')
for test_name in failures:
    print(f'TEST CLASS: {test_name}')
    tree = ET.parse(f'{sys.argv[2]}/TEST-{test_name}.xml')
    tree = next(tree.iter('testsuite'))
    for test_case in tree.iter('testcase'):
        print(f'TEST NAME: {test_case.attrib["name"]}')
        for failure in test_case.iter('failure'):
            print(f'FAILURE:\n{node_text(failure)}')
        for error in test_case.iter('error'):
            print(f'ERROR:\n{node_text(error)}')
    for output in tree.iter('system-out'):
        print(f'SYSTEM.OUT:\n{node_text(output)}')
    for err_output in tree.iter('system-err'):
        print(f'SYSTEM.ERR:\n{node_text(err_output)}')
    print()

