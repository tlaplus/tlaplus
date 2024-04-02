from dataclasses import dataclass
import re
import sys
import xml.etree.ElementTree as ET

example = '[junit] Tests run: 1, Failures: 0, Errors: 0, Skipped: 0, Time elapsed: 0.209 sec, Thread: 7, Class: pcal.CallGotoUnlabeledTest'
pattern = re.compile(
    '\[junit\] Tests run: (?P<run_count>\d+), '
    + 'Failures: (?P<failure_count>\d+), '
    + 'Errors: (?P<error_count>\d+), '
    + 'Skipped: (?P<skip_count>\d+), '
    + 'Time elapsed: (?P<runtime>\d+\.\d+) sec, '
    + 'Thread: (?P<thread_id>\d+), '
    + 'Class: (?P<test_name>.+)'
)

@dataclass
class TestReport:
    run_count: int
    failure_count: int
    error_count: int
    skip_count: int
    runtime: float
    thread_id: int
    name: str

def match_to_report(match):
    return TestReport(
        int(match.group('run_count')),
        int(match.group('failure_count')),
        int(match.group('error_count')),
        int(match.group('skip_count')),
        float(match.group('runtime')),
        int(match.group('thread_id')),
        match.group('test_name')
    )

reports = []
with open(sys.argv[1], 'r') as f:
    reports = [
        match_to_report(match)
        for line in f
        if (match := pattern.search(line)) is not None
    ]

reports = sorted(reports, key=lambda report: report.runtime, reverse=True)

print(f'Test count: {len(reports)}')

def node_text(node):
    text = node.text
    return text.strip() if text is not None else None

print('Failures:\n')
failures = [report.name for report in reports if report.failure_count > 0]
for test_name in failures:
    print(f'TEST CLASS: {test_name}')
    tree = ET.parse(f'{sys.argv[2]}/TEST-{test_name}.xml')
    tree = next(tree.iter('testsuite'))
    for test_case in tree.iter('testcase'):
        print(f'TEST NAME: {test_case.attrib["name"]}')
        for failure in test_case.iter('failure'):
            print(f'FAILURE:\n{node_text(failure)}')
    for output in tree.iter('system-out'):
        print(f'SYSTEM.OUT:\n{node_text(output)}')
    for err_output in tree.iter('system-err'):
        print(f'SYSTEM.ERR:\n{node_text(err_output)}')
    print()

print('Longest-running tests:')
for report in reports[slice(20)]:
    print(f'{report.runtime:5.1f} sec | {report.name}')

