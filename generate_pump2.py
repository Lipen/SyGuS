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
    0: {'critical': [39, 18, 51], 'highwater': [1, 11]},
    1: {'highwater': [52], 'switch_pump_on': [2]},
    2: {'turn_on': [3, 95]},
    3: {'critical': [4], 'low_water': [24]},
    4: {'switch_pump_off': [5]},
    5: {'turn_off': [0, 62]},
    6: {'switch_pump_on': [7]},
    7: {'turn_on': [8, 96]},
    8: {'critical': [9], 'low_water': [17]},
    9: {'switch_pump_off': [10]},
    10: {'turn_off': [27, 18]},
    11: {'critical': [11], 'highwater': [13, 111], 'not_critical': [113]},
    12: {'critical': [117], 'not_critical': [113]},
    13: {'not_critical': [14]},
    14: {'switch_pump_on': [15]},
    15: {'turn_on': [16]},
    16: {'low_water': [43]},
    17: {'switch_pump_off': [5]},
    18: {'critical': [0, 82], 'highwater': [38], 'not_critical': [97]},
    19: {'switch_pump_on': [20]},
    20: {'turn_on': [21]},
    21: {'critical': [24], 'low_water': [56]},
    22: {'critical': [63], 'low_water': [74]},
    23: {'critical': [34], 'low_water': [74]},
    24: {'switch_pump_off': [25]},
    25: {'turn_off': [1, 55]},
    26: {'critical': [86], 'low_water': [4]},
    27: {'critical': [18], 'highwater': [6]},
    28: {'highwater': [29]},
    29: {'switch_pump_on': [81]},
    30: {'low_water': [31]},
    31: {'switch_pump_off': [32]},
    32: {'turn_off': [33, 101]},
    33: {'highwater': [113]},
    34: {'switch_pump_off': [35]},
    35: {'turn_off': [62, 12]},
    36: {'highwater': [67], 'switch_pump_on': [116]},
    37: {'critical': [63], 'low_water': [99]},
    38: {'switch_pump_on': [20]},
    39: {'highwater': [51]},
    40: {'critical': [40, 51]},
    41: {'turn_on': [112, 42]},
    42: {'critical': [43], 'low_water': [63]},
    43: {'switch_pump_off': [44]},
    44: {'turn_off': [45, 49]},
    45: {'critical': [55], 'not_critical': [46]},
    46: {'switch_pump_on': [47]},
    47: {'turn_on': [112]},
    48: {'switch_pump_off': [69]},
    49: {'critical': [117], 'highwater': [70]},
    50: {'turn_off': [73]},
    51: {'critical': [51, 40], 'not_critical': [1]},
    52: {'switch_pump_on': [53]},
    53: {'turn_on': [26, 3]},
    54: {'critical': [55]},
    55: {'critical': [55], 'highwater': [105], 'not_critical': [36]},
    56: {'switch_pump_off': [57]},
    57: {'turn_off': [102, 11]},
    58: {'switch_pump_off': [59]},
    59: {'turn_off': [60]},
    60: {'critical': [60], 'not_critical': [67]},
    61: {'turn_on': [65, 68]},
    62: {'critical': [84, 0], 'highwater': [36], 'not_critical': [6]},
    63: {'switch_pump_off': [64]},
    64: {'turn_off': [97, 104]},
    65: {'critical': [34], 'low_water': [92]},
    66: {'highwater': [67]},
    67: {'switch_pump_on': [61]},
    68: {'low_water': [48]},
    69: {'turn_off': [49]},
    70: {'highwater': [105], 'switch_pump_on': [71]},
    71: {'turn_on': [22, 103]},
    72: {'switch_pump_off': [50]},
    73: {'highwater': [70]},
    74: {'switch_pump_off': [75]},
    75: {'turn_off': [55]},
    76: {'low_water': [77]},
    77: {'switch_pump_off': [78]},
    78: {'turn_off': [79, 109]},
    79: {'highwater': [80]},
    80: {'switch_pump_on': [107]},
    81: {'turn_on': [26, 30]},
    82: {'critical': [51], 'not_critical': [97]},
    83: {'critical': [56], 'low_water': [99]},
    84: {'critical': [84], 'highwater': [54], 'not_critical': [85]},
    85: {'switch_pump_on': [81]},
    86: {'switch_pump_off': [87]},
    87: {'turn_off': [88, 28]},
    88: {'critical': [11], 'not_critical': [89]},
    89: {'switch_pump_on': [90]},
    90: {'turn_on': [91]},
    91: {'critical': [92]},
    92: {'switch_pump_off': [93]},
    93: {'turn_off': [94, 66]},
    94: {'critical': [11], 'not_critical': [1]},
    95: {'critical': [77], 'low_water': [9]},
    96: {'critical': [99], 'low_water': [86]},
    97: {'highwater': [97], 'switch_pump_on': [98]},
    98: {'turn_on': [65, 96]},
    99: {'switch_pump_off': [100]},
    100: {'turn_off': [11, 18]},
    101: {'critical': [101], 'not_critical': [19]},
    102: {'critical': [102], 'not_critical': [111]},
    103: {'critical': [9], 'low_water': [72]},
    104: {'critical': [88], 'not_critical': [105]},
    105: {'switch_pump_on': [106]},
    106: {'turn_on': [23, 76]},
    107: {'turn_on': [108, 68]},
    108: {'critical': [63], 'low_water': [72]},
    109: {'critical': [110]},
    110: {'not_critical': [80]},
    111: {'switch_pump_on': [41]},
    112: {'critical': [58], 'low_water': [56]},
    113: {'highwater': [38], 'switch_pump_on': [114]},
    114: {'turn_on': [115]},
    115: {'critical': [31], 'low_water': [34]},
    116: {'turn_on': [83, 37]},
    117: {'critical': [118], 'not_critical': [70]},
    118: {'not_critical': [70]}
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
    current_state = 0

    for line in f:
        line = line.rstrip()
        if line == 'trace':
            if trace:
                traces.append(trace)
                trace = []
                current_state = 0
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
        possible_states = list(sum(automaton[state].values(), []))
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
