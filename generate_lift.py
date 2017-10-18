import os
import time
import regex
import textwrap
import subprocess
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor, as_completed
from collections import defaultdict

path_traces = Path('traces/liftDoors')
path_sygus_template = 'sygus/infer_lift_{}.sy'
path_inferred = Path('done/inferred_lift.sy')
os.makedirs(os.path.dirname(path_inferred), exist_ok=True)

sygus_logic = 'LIA'
compress_round = 3
infer_regex = r'\(define-fun (?P<func_name>\w+) \((?:\((?P<arg_name>\w+) (?P<arg_type>\w+)\) ?)*\) (?P<ret_type>\w+) (?P<body>.*)\)'
infer_pattern = regex.compile(infer_regex)
time_start = time.time()


def get_funcname(state):
    return f'{state}'


print('[*] Reading traces from <{}>...'.format(path_traces))
with path_traces.open() as f:
    print('[*] Skipping types...')
    for line in f:
        if line.rstrip() == 'trace':
            break
    else:
        print('[!] No traces!')
        exit(1)

    # - -- --- -- - -- --- -- - -- --- -- - -- --- -- - -- --- -- -

    print('[*] Parsing traces...')
    trace = []  # (state_from, state_to, (water, methane, pump))
    traces = []  # [trace]
    current_state = 1

    for line in f:
        line = line.rstrip()
        if line == 'trace':
            if trace:
                traces.append(trace)
                trace = []
                current_state = 1
            else:
                print('[!] Empty trace')
            continue

        label, t = line.split()
        t = int(float(t))
        trace.append((label, t))
    if trace:
        traces.append(trace)
    else:
        print('[!] Empty trace')

    print('[+] Total traces: {}'.format(len(traces)))

# - -- --- -- - -- --- -- - -- --- -- - -- --- -- - -- --- -- -

print('[*] Generating constraints...')
constraints = defaultdict(list)  # {state_from: [(state_to, (water, methane, pump))]}
for trace in traces:
    for (label, t), (_, t_next) in zip(trace, trace[1:]):
        constraints[label].append((t, t_next))

print('[+] Total constraints: {}'.format(sum(map(len, constraints.values()))))

# - -- --- -- - -- --- -- - -- --- -- - -- --- -- - -- --- -- -

print('[*] Compressing constraints...')

constraints = {label: list(set(constraint)) for label, constraint in constraints.items()}

print('[+] Total compressed constraints: {}'.format(sum(map(len, constraints.values()))))

# - -- --- -- - -- --- -- - -- --- -- - -- --- -- - -- --- -- -


def write_sygus(label):
    function_name = get_funcname(label)
    path_sygus = Path(path_sygus_template.format(function_name))

    print(f'[.] {function_name}: writing SyGuS to <{path_sygus}>...')
    # print(f'[.] State #{state}: using {sygus_logic} logic')

    with path_sygus.open('w') as f:
        f.write('(set-logic {})\n\n'.format(sygus_logic))

        print(f'[.] {function_name}: writing synth-fun...')
        arguments = '(t Int)'
        allowed_values = [0, 1, 3, 5, 10]
        allowed_values = ' '.join(map(str, allowed_values))

        s = f'''
        (synth-fun {function_name} ({arguments}) Int (
            (Start Int (
                IntExpr
            ))
            (BoolExpr Bool (
                (Variable Bool)
                (not BoolExpr)
                (and BoolExpr BoolExpr)
                (<= IntExpr IntExpr)
            ))
            (IntExpr Int (
                {allowed_values}
                (Variable Int)
                (+ IntExpr IntExpr)
                (- IntExpr IntExpr)
                (* IntExpr IntExpr)
                (ite BoolExpr IntExpr IntExpr)
            ))
        ))'''
        f.write(textwrap.dedent(s).strip() + '\n\n')

        print('[.] {function_name}: writing constraints...')
        for t, answer in constraints[label]:
            f.write(f'(constraint (= ({function_name} {t}) {answer}))\n')

        f.write('\n(check-synth)\n')
        print(f'[+] {function_name}: done')


def infer(label):
    path = Path(path_sygus_template.format(get_funcname(label)))
    cmd = f'cvc4-stable {path}'
    process = subprocess.run(cmd, shell=True, stdout=subprocess.PIPE)
    # Although there should be just two lines ("unsat" and "(define-fun ...") lets try to parse "all" definitions
    for m in infer_pattern.finditer(process.stdout.decode()):
        func_name = m.group('func_name')
        arg_names = ' '.join(m.captures('arg_name'))
        ret_type = m.group('ret_type')
        arg_types = ' -> '.join(m.captures('arg_type') + [ret_type])
        body = m.group('body')
        s = f'{func_name} :: {arg_types}\n{func_name} {arg_names} = {body}'
        yield s


def process(label):
    write_sygus(label)
    synthesized_functions = list(infer(label))
    return synthesized_functions


print('[*] Submitting tasks to pool...')
with ThreadPoolExecutor() as executor:
    tasks = {executor.submit(process, label): label for label in 'setTimer waitTimer systemInitReady closingDoor buttonInterrupted openingDoor fullyOpen fullyClosed requestOpen timeout'.split()}

    with path_inferred.open('w') as f:
        for future in as_completed(tasks):
            label = tasks[future]
            synthesized_functions = future.result()
            print(f'[+] Dumping synthesized function(s) for label <{label}>.')
            for synfunc in synthesized_functions:
                f.write(f'{synfunc}\n')

# - -- --- -- - -- --- -- - -- --- -- - -- --- -- - -- --- -- -

print('[+] Done in {:.3f}s'.format(time.time() - time_start))
