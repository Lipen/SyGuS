filename_traces = 'traces/liftDoors'
filename_sygus = 'sygus/infer_lift.sy'

with open(filename_traces) as ft, open(filename_sygus, 'w') as fs:
    variables = set()
    flag = 0
    # 0 -- searching for 'types' line
    # 1 -- parsing types
    # 2 -- parsing trace
    traces = []
    trace = []
    constraints = set()

    print('[*] Reading traces from <{}>...'.format(filename_traces))

    for line in ft:
        line = line.rstrip()

        if flag == 0:
            if line == 'types':
                flag = 1
        elif flag == 1:
            if line == 'trace':
                flag = 2
                continue

            variables.add(line.split()[0])
        elif flag == 2:
            if line == 'trace':
                if trace:
                    traces.append(trace)
                    trace = []
                continue

            variable, t = line.split()
            t = int(float(t))

            trace.append((variable, t))

    if trace:
        traces.append(trace)

    print('[*] Generating constraints...')

    for trace in traces:
        for (variable, t), (_, t_next) in zip(trace, trace[1:]):
            constraints.add((variable, t, t_next))

    print('[*] Writing SyGuS to <{}>...'.format(filename_sygus))

    fs.write('(set-logic LRA)\n\n')

    for function_name in 'setTimer waitTimer systemInitReady closingDoor buttonInterrupted openingDoor fullyOpen fullyClosed requestOpen timeout'.split():
        fs.write('(synth-fun {} ((t Int)) Int\n'.format(function_name) +
                 '    ((Start Int\n'
                 '        (0 1 3 5 10 t\n'
                 '         (+ Start Start)\n'
                 '         (- Start Start)\n'
                 # '         (* Start Start)\n'
                 # '         (/ Start Start)))))\n')
                 '         (* Start Start)))))\n')

    fs.write('\n')

    for constraint in sorted(constraints):
        name, t_in, t_out = constraint
        # print('[*] New constraint: {}({}) = {}'.format(name, t_in, t_out))
        fs.write('(constraint (= ({} {}) {}))\n'.format(name, t_in, t_out))

    fs.write('\n(check-synth)\n')

    print('[+] Done writing SyGuS!')
