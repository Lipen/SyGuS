import time
from decimal import Decimal

filename_traces = 'traces/minePump'
filename_sygus = 'sygus/infer_pump.sy'

sygus_logic = 'Reals'
compress_round = 3


def state2funcname(x):
    # return 'state' + chr(ord('A') + x - 1)
    return 'state{}'.format(x)


with open(filename_traces) as ft, open(filename_sygus, 'w') as fs:
    traces = []  # [trace]
    trace = []  # (state_from, state_to, (water, methane, pump))
    constraints = []  # [trace]
    current_state = 1

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

    print('[*] Reading traces from <{}>...'.format(filename_traces))
    time_start = time.time()

    print('[*] Skipping types...')
    for line in ft:
        if line.rstrip() == 'trace':
            break
    else:
        print('[!] No traces!')
        exit(1)

    # - -- --- -- - -- --- -- - -- --- -- - -- --- -- - -- --- -- -

    print('[*] Parsing traces...')
    for line in ft:
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
    for trace in traces:
        for event in trace:
            constraints.append(event)

    print('[+] Total constraints: {}'.format(len(constraints)))

    # - -- --- -- - -- --- -- - -- --- -- - -- --- -- - -- --- -- -

    print('[*] Compressing constraints by rounding to {} digit...'.format(compress_round))

    constraints = {(sf, st, (round(w, compress_round), round(m, compress_round), p)) for sf, st, (w, m, p) in constraints}

    print('[*] Total compressed constraints: {}'.format(len(constraints)))

    # - -- --- -- - -- --- -- - -- --- -- - -- --- -- - -- --- -- -

    print('[*] Writing SyGuS to <{}>...'.format(filename_sygus))
    print(' >  Using {} logic'.format(sygus_logic))
    fs.write('(set-logic {})\n\n'.format(sygus_logic))
    fs.write('(define-sort State () Int)\n\n')

    print(' >  Writing synth-fun declarations...')
    for state in sorted(automaton):
        function_name = state2funcname(state)
        arguments = '(water Real) (methane Real) (pump Bool)'
        possible_states = list(automaton[state].values())
        start_block = ''
        for ps in possible_states[:-1]:
            start_block += '(ite BoolExpr {} '.format(ps)
        start_block += str(possible_states[-1]) + ')' * (len(possible_states) - 1)
        allowed_values = [600]

        # state_water = {}
        # for state_from, state_to, (water, _, _) in constraints:
        #     if state_from == state:
        #         if state_to in state_water:
        #             state_water[state_to].append(water)
        #         else:
        #             state_water[state_to] = [water]
        # state_methane = {}
        # for state_from, state_to, (_, methane, _) in constraints:
        #     if state_from == state:
        #         if state_to in state_methane:
        #             state_methane[state_to].append(methane)
        #         else:
        #             state_methane[state_to] = [methane]
        # state_water_min = {state_to: min(item) for state_to, item in state_water.items()}
        # state_water_max = {state_to: max(item) for state_to, item in state_water.items()}
        # state_methane_min = {state_to: min(item) for state_to, item in state_methane.items()}
        # state_methane_max = {state_to: max(item) for state_to, item in state_methane.items()}
        # for state_to in automaton[state].values():
        #     for state_water_ in state_water_min, state_water_max, state_methane_min, state_methane_max:
        #         allowed_values.append('(/ {} {})'.format(*Decimal(state_water_[state_to]).as_integer_ratio()))

        f = ('(synth-fun {function_name} ({arguments}) State (',
             '    (Start State (',
             '        {start_block}',
             '    ))',
             '    (BoolExpr Bool (',
             '        (Variable Bool)',
             '        (not BoolExpr)',
             '        (and BoolExpr BoolExpr)',
             '        (<= RealExpr RealExpr)',
             '    ))',
             '    (RealExpr Real (',
             '        {allowed_values}',
             '        (Variable Real)',
             # '        (+ RealExpr RealExpr)',
             # '        (- RealExpr RealExpr)',
             # '        (* RealExpr RealExpr)',
             # '        (/ RealExpr RealExpr)',
             '        (ite BoolExpr RealExpr RealExpr)',
             '    ))',
             '))\n')
        fs.write('\n'.join(f).format(function_name=function_name, arguments=arguments, start_block=start_block, allowed_values=' '.join(map(str, allowed_values))))

    fs.write('\n')

    # - -- --- -- - -- --- -- - -- --- -- - -- --- -- - -- --- -- -

    print(' >  Writing constraints...')
    for state_from, state_to, (water, methane, pump) in sorted(constraints):
        # DEBUG
        # if state_from != 1:
        #     continue
        # DEBUG
        function_name = state2funcname(state_from)
        arguments = '{} {} {}'.format(water, methane, pump).lower()
        fs.write('(constraint (= ({} {}) {}))\n'.format(function_name, arguments, state_to))

    fs.write('\n(check-synth)\n')

    # fs.write('\n(get-info :reason-unknown)\n')
    # fs.write('\n(get-assignment)\n')
    # fs.write('\n(get-unsat-core)\n')

    print('[+] Done writing SyGuS in {:.3f}s'.format(time.time() - time_start))
