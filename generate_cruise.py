from collections import defaultdict, OrderedDict

filename_traces = 'traces/cruiseControl'
filename_sygus = 'sygus/infer_cruise.sy'


def type2callback(t):
    if t == 'N':
        return float
        # return lambda x: int(float(x))
    elif t == 'S':
        return lambda x: x == 'true'
    elif t == 'NI':
        return int
    else:
        raise ValueError('Unknown type <{}>'.format(t))


def type2str(t):
    if t == 'N':
        return 'Real'
        # return 'Int'
    elif t == 'S':
        return 'Bool'
    elif t == 'NI':
        return 'Int'
    else:
        raise ValueError('Unknown type <{}>'.format(t))


with open(filename_traces) as ft, open(filename_sygus, 'w') as fs:
    types = defaultdict(OrderedDict)  # {event: {variable: type}}
    traces = []  # [trace]
    trace = []  # (event, {variable: value})
    constraints = []  # [(event, values_old, values_new)]

    print('[*] Reading traces from <{}>...'.format(filename_traces))

    print('[*] Parsing types...')
    for line in ft:
        line = line.rstrip()
        if line == 'types':
            continue
        if line == 'trace':
            break

        event, *var_types = line.split()
        for item in var_types:
            variable, var_type = item.split(':')
            types[event][variable] = var_type
    else:
        print('[!] No traces!')
        exit(1)

    print('[*] Parsing traces...')
    for line in ft:
        line = line.rstrip()
        if line == 'trace':
            if trace:
                traces.append(trace)
                trace = []
            else:
                print('[!] Empty trace')
            continue

        event, *values_raw = line.split()
        values = OrderedDict()  # {variable: value}
        for value, (variable, var_type) in zip(values_raw, types[event].items()):
            values[variable] = type2callback(var_type)(value)
        trace.append((event, values))
    if trace:
        traces.append(trace)
    else:
        print('[!] Empty trace')

    print('[*] Generating constraints...')
    for trace in traces:
        for (event, values), (_, values_next) in zip(trace, trace[1:]):
            values_new = OrderedDict()
            for variable, value in values.items():
                values_new[variable] = values_next.get(variable, value)
            constraints.append((event, values, values_new))

    print('[*] Writing SyGuS to <{}>...'.format(filename_sygus))
    # fs.write('(set-option :produce-assignments true) \n\n')
    # fs.write('(set-option :produce-unsat-cores true) \n\n')
    fs.write('(set-logic LRA)\n\n')

    for event, var_types in types.items():
        arguments = ''.join('({} {})'.format(variable, type2str(var_type)) for variable, var_type in var_types.items())
        variable_names_real = ' '.join(filter(lambda variable: type2str(var_types[variable]) == 'Real', var_types.keys()))
        variable_names_bool = ' '.join(filter(lambda variable: type2str(var_types[variable]) == 'Bool', var_types.keys()))
        variable_names_int = ' '.join(filter(lambda variable: type2str(var_types[variable]) == 'Int', var_types.keys()))
        for variable, var_type in var_types.items():
            function_name = '{}_{}'.format(event, variable)
            return_type = type2str(var_type)
            fs.write('(synth-fun {} ({}) {}\n'.format(function_name, arguments, return_type))
            if return_type == 'Real':
                fs.write('    ((Start Real\n'
                         '        (0 1 2 {} {}\n'.format(variable_names_real, variable_names_int) +
                         '         (+ Start Start)\n'
                         '         (- Start Start)\n'
                         '         (* Start Start)\n'
                         '         (/ Start Start)\n'
                         '         (ite StartBool Start Start)))\n'
                         '     (StartBool Bool\n'
                         '        ({}\n'.format(variable_names_bool) +
                         '         (and StartBool StartBool)\n'
                         '         (not StartBool)\n'
                         '         (<= Start Start)))))\n')
            elif return_type == 'Int':
                fs.write('    ((Start Int\n'
                         '        (0 1 2 {}\n'.format(variable_names_int) +
                         '         (+ Start Start)\n'
                         '         (- Start Start)\n'
                         '         (* Start Start)\n'
                         '         (ite StartBool Start Start)))\n'
                         '     (StartBool Bool\n'
                         '        ({}\n'.format(variable_names_bool) +
                         '         (and StartBool StartBool)\n'
                         '         (not StartBool)\n'
                         '         (<= Start Start)))))\n')
            elif return_type == 'Bool':
                fs.write('    ((Start Bool\n'
                         '        ({}\n'.format(variable_names_bool) +
                         '         (and Start Start)\n'
                         '         (not Start)'
                         '         (<= StartReal StartReal)))\n'
                         '     (StartReal Real\n'
                         '        (0 1 2 {} {}\n'.format(variable_names_real, variable_names_int) +
                         '         (+ StartReal StartReal)\n'
                         '         (- StartReal StartReal)\n'
                         '         (* StartReal StartReal)\n'
                         '         (/ StartReal StartReal)\n'
                         '         (ite Start StartReal StartReal)))))\n')

    fs.write('\n')

    for constraint in constraints:
        event, values_old, values_new = constraint
        var_types = types[event]
        arguments = ' '.join(map(str, values_old.values())).lower()
        for variable in values_old.keys():
            value_old = values_old[variable]
            value_new = values_new[variable]
            var_type = var_types[variable]
            function_name = '{}_{}'.format(event, variable)
            if type2str(var_type) == 'Real':
                fs.write('(constraint (let ((e (- ({} {}) {}))) (ite (> e 0) (<= e 0.01) (<= (- e) 0.01))))\n'.format(function_name, arguments, value_new))
                pass
            elif type2str(var_type) == 'Int':
                fs.write('(constraint (= ({} {}) {}))\n'.format(function_name, arguments, value_new))
                pass
            elif type2str(var_type) == 'Bool':
                if values_new:
                    fs.write('(constraint ({} {}))\n'.format(function_name, arguments))
                else:
                    fs.write('(constraint (not ({} {})))\n'.format(function_name, arguments))

    fs.write('\n(check-synth)\n')

    # fs.write('\n(get-info :reason-unknown)\n')
    # fs.write('\n(get-assignment)\n')
    # fs.write('\n(get-unsat-core)\n')

    print('[+] Done writing SyGuS!')
