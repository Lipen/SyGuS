import os
import time
import regex
import textwrap
import subprocess
from pathlib import Path
from decimal import Decimal
from concurrent.futures import ThreadPoolExecutor, as_completed
from collections import defaultdict

path_traces = Path('traces/minePump')
path_sygus_template = 'sygus/infer_pump_{}.sy'
path_inferred = Path('done/inferred_pump.sy')
os.makedirs(os.path.dirname(path_inferred), exist_ok=True)

sygus_logic = 'Reals'
compress_round = 3
infer_regex = r'\(define-fun (?P<func_name>\w+) \((?:\((?P<arg_name>\w+) (?P<arg_type>\w+)\) ?)*\) (?P<ret_type>\w+) (?P<body>.*)\)'
infer_pattern = regex.compile(infer_regex)
time_start = time.time()


def state2funcname(x):
    # return 'state' + chr(ord('A') + x - 1)
    return 'state{}'.format(x)


#   Int :: 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15
# State :: A B C D E F G H I J  K  L  M  N  O
automaton = {  # {state_from: {label: state_to}}
    1: {'highwater': 2, 'critical': 3},
    2: {'switch_pump_on': 4},
    3: {'not_critical': 5, 'highwater': 6},
    4: {'turn_on': 7},
    5: {'highwater': 8},
    6: {'critical': 6, 'not_critical': 9},
    7: {'low_water': 10, 'critical': 11},
    8: {'switch_pump_on': 12},
    9: {'switch_pump_on': 15},
    10: {'switch_pump_off': 13},
    11: {'switch_pump_off': 14},
    12: {'turn_on': 7},
    13: {'turn_off': 1},
    14: {'turn_off': 6},
    15: {'turn_on': 7}
}

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

        label, water, methane, pump = line.split()
        water = Decimal(water)
        methane = Decimal(methane)
        pump = bool(pump)
        new_state = automaton[current_state][label]
        trace.append((current_state, new_state, (water, methane, pump)))
        current_state = new_state
    if trace:
        traces.append(trace)
    else:
        print('[!] Empty trace')

    print('[+] Total traces: {}'.format(len(traces)))

# - -- --- -- - -- --- -- - -- --- -- - -- --- -- - -- --- -- -

print('[*] Generating constraints...')
constraints = defaultdict(list)  # {state_from: [(state_to, (water, methane, pump))]}
for trace in traces:
    for state_from, state_to, (water, methane, pump) in trace:
        constraints[state_from].append((state_to, (water, methane, pump)))

print('[+] Total constraints: {}'.format(sum(len(item) for item in constraints.values())))

# - -- --- -- - -- --- -- - -- --- -- - -- --- -- - -- --- -- -

print('[*] Compressing constraints by rounding to {} digit...'.format(compress_round))

constraints = {state_from: [(state_to, (round(water, compress_round), round(methane, compress_round), pump)) for state_to, (water, methane, pump) in xxx] for state_from, xxx in constraints.items()}

print('[*] Total compressed constraints: {}'.format(sum(len(item) for item in constraints.values())))

# - -- --- -- - -- --- -- - -- --- -- - -- --- -- - -- --- -- -


def write_sygus(state):
    function_name = state2funcname(state)
    path_sygus = Path(path_sygus_template.format(function_name))

    print(f'[.] State #{state}: writing SyGuS to <{path_sygus}>...')
    # print(f'[.] State #{state}: using {sygus_logic} logic')

    with path_sygus.open('w') as f:
        f.write('(set-logic {})\n\n'.format(sygus_logic))
        f.write('(define-sort State () Int)\n\n')

        print(f'[.] State #{state}: writing synth-fun...')
        arguments = '(water Real) (methane Real) (pump Bool)'
        possible_states = list(automaton[state].values())
        start_block = ''
        for ps in possible_states[:-1]:
            start_block += f'(ite BoolExpr {ps} '
        ll = len(possible_states) - 1
        start_block += str(possible_states[-1]) + ')' * ll
        allowed_values = [600]
        allowed_values = ' '.join(map(str, allowed_values))

        s = f'''
        (synth-fun {function_name} ({arguments}) State (
            (Start State (
                {start_block}
            ))
            (BoolExpr Bool (
                (Variable Bool)
                (not BoolExpr)
                (and BoolExpr BoolExpr)
                (<= RealExpr RealExpr)
            ))
            (RealExpr Real (
                {allowed_values}
                (Variable Real)
                (ite BoolExpr RealExpr RealExpr)
            ))
        ))'''
        f.write(textwrap.dedent(s).strip() + '\n\n')

        print('[.] State #{state}: writing constraints...')
        for state_to, (water, methane, pump) in constraints[state]:
            arguments = '{} {} {}'.format(water, methane, pump).lower()
            f.write(f'(constraint (= ({function_name} {arguments}) {state_to}))\n')

        f.write('\n(check-synth)\n')
        print(f'[+] State #{state}: done')


def infer(state):
    path = Path(path_sygus_template.format(state2funcname(state)))
    cmd = f'cvc4-stable {path}'
    process = subprocess.run(cmd, shell=True, stdout=subprocess.PIPE)
    # Although there should be just two lines ("unsat" and "(define-fun ...") lets try to parse "all" definitions
    for m in infer_pattern.finditer(process.stdout.decode()):
        func_name = m.group('func_name')
        arg_names = ' '.join(m.captures('arg_name'))
        # ret_type = m.group('ret_type')
        ret_type = 'State'
        arg_types = ' -> '.join(m.captures('arg_type') + [ret_type])
        body = m.group('body')
        s = f'{func_name} :: {arg_types}\n{func_name} {arg_names} = {body}'
        yield s


def process(state):
    write_sygus(state)
    synthesized_functions = list(infer(state))
    return synthesized_functions


print('[*] Submitting tasks to pool...')
with ThreadPoolExecutor() as executor:
    tasks = {executor.submit(process, state): state for state in automaton}

    with path_inferred.open('w') as f:
        for future in as_completed(tasks):
            state = tasks[future]
            synthesized_functions = future.result()
            print(f'[+] Dumping synthesized function(s) for state #{state}.')
            for synfunc in synthesized_functions:
                f.write(f'{synfunc}\n\n')

# - -- --- -- - -- --- -- - -- --- -- - -- --- -- - -- --- -- -

print('[+] Done in {:.3f}s'.format(time.time() - time_start))
