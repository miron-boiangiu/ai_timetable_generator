import sys
import json
import os
import copy
import random

from ast import literal_eval
from heapq import heappop, heappush
from check_constraints import *
from utils import *

# Parameters
CSP_DELTA_ITERATIONS_UNTIL_TIMEOUT = 500000

# State macros
PROF_INTERVALS_NO = "_PROF_INTERVALS_NO"
STUDENTS_TO_ASSIGN_PER_SUBJECT = "_STUDENTS_LEFT_TO_ASSIGN"
ENTRIES_NO = "_ENTRIES_NO"
WEAK_CONSTRAINTS = "_WEAK_CONSTRAINTS"


def all_covered(state, timetable_specs):
    # Considering the state is valid, are all subjects covered?

    for materie, studenti_ramasi in state[STUDENTS_TO_ASSIGN_PER_SUBJECT].items():
        if studenti_ramasi > 0:
            return False

    return True


def pick_subject(state, subject_order):

    possible_subjects = [subject for subject in subject_order if state[STUDENTS_TO_ASSIGN_PER_SUBJECT][subject] > 0]
    return possible_subjects[0]


def deepcopy_timetable(timetable, timetable_specs):  # The one from the 'copy' module is slower.
    new_timetable = {}

    new_timetable[WEAK_CONSTRAINTS] = timetable[WEAK_CONSTRAINTS]
    new_timetable[ENTRIES_NO] = timetable[ENTRIES_NO]
    
    new_timetable[STUDENTS_TO_ASSIGN_PER_SUBJECT] = {}
    for subject, no_stud in timetable[STUDENTS_TO_ASSIGN_PER_SUBJECT].items():
        new_timetable[STUDENTS_TO_ASSIGN_PER_SUBJECT][subject] = no_stud

    new_timetable[PROF_INTERVALS_NO] = {}
    for prof, int_no in timetable[PROF_INTERVALS_NO].items():
        new_timetable[PROF_INTERVALS_NO][prof] = int_no

    for day in timetable_specs[ZILE]:
        new_timetable[day] = {}
        for interval in timetable[day]:
            new_timetable[day][interval] = {}
            for sala, tup in timetable[day][interval].items():
                new_timetable[day][interval][sala] = tup

    return new_timetable 


def state_neighbours(state, timetable_specs, subject_order):

    unfinished_subject = pick_subject(state, subject_order)
    valid_profs = [prof for prof in timetable_specs[PROFESORI].keys() if unfinished_subject in timetable_specs[PROFESORI][prof][MATERII]]
    valid_profs = list(filter(lambda prof: state[PROF_INTERVALS_NO][prof] > 0, valid_profs))
    valid_classrooms = [classroom for classroom in timetable_specs[SALI].keys() if unfinished_subject in timetable_specs[SALI][classroom][MATERII]]

    new_states = []

    for day in timetable_specs[ZILE]:
        for interval in state[day]:
            interval_str = str(interval)

            profs_in_interval = [tup[0] for sala, tup in state[day][interval].items()]
            available_profs = [prof for prof in valid_profs if prof not in profs_in_interval]

            for classroom in valid_classrooms:

                if classroom in state[day][interval]:
                    continue

                for prof in available_profs:
                    new_state = deepcopy_timetable(state, timetable_specs)
                    new_state[ENTRIES_NO] += 1
                    new_state[day][interval][classroom] = (prof, unfinished_subject)
                    new_state[STUDENTS_TO_ASSIGN_PER_SUBJECT][unfinished_subject] -= timetable_specs[SALI][classroom][CAPACITATE]
                    new_state[PROF_INTERVALS_NO][prof] -= 1

                    for constrangere in timetable_specs[PROFESORI][prof][CONSTRANGERI]:
                        if constrangere[0] != "!":
                            continue

                        if constrangere[1:] == day:
                            new_state[WEAK_CONSTRAINTS] += 1
                            continue

                        if "-" in constrangere:
                            parsed_interval = parse_interval(constrangere[1:])

                            if parsed_interval[0] <= interval[0] and interval[1] <= parsed_interval[1]:
                                new_state[WEAK_CONSTRAINTS] += 1

                    new_states.append(new_state)

    new_states.sort(key=lambda a: a[WEAK_CONSTRAINTS], reverse=True)
    return new_states


def h(state, timetable_specs, min_classroom_size):
    min_classroom_size /= 5
    unfinished_subjects = [tup for tup in state[STUDENTS_TO_ASSIGN_PER_SUBJECT].items() if tup[1] > 0]

    if len(unfinished_subjects) == 0:
        return 0

    leftover_students = sum(map(lambda a: a[1], unfinished_subjects))
    return (leftover_students / min_classroom_size) + 2 * state[WEAK_CONSTRAINTS]


def g(state):
    return state[ENTRIES_NO]


def generate_initial_timetable(timetable_specs):
    timetable = {}

    for day in timetable_specs[ZILE]:
        timetable[day] = {}

        for interval in timetable_specs[INTERVALE]:
            interval = literal_eval(interval)
            timetable[day][interval] = {}

    timetable[WEAK_CONSTRAINTS] = 0
    timetable[ENTRIES_NO] = 0

    timetable[STUDENTS_TO_ASSIGN_PER_SUBJECT] = {}
    for subject, students_needed in timetable_specs[MATERII].items():
        timetable[STUDENTS_TO_ASSIGN_PER_SUBJECT][subject] = students_needed

    timetable[PROF_INTERVALS_NO] = {}
    for prof in timetable_specs[PROFESORI]:
        timetable[PROF_INTERVALS_NO][prof] = 7
    
    return timetable


def generate_subject_order(timetable_specs):
    subject_to_prof_score = {}
    subject_to_class_score = {}
    final_scores = []

    for subject in timetable_specs[MATERII]:
        subject_to_prof_score[subject] = 0
        subject_to_class_score[subject] = 0
    
    for sala, sala_specs in timetable_specs[SALI].items():
        for materie in sala_specs[MATERII]:
            subject_to_class_score[materie] += 1 / len(sala_specs[MATERII])

    for prof, prof_specs in timetable_specs[PROFESORI].items():
        for materie in prof_specs[MATERII]:
            subject_to_prof_score[materie] += 1 / len(timetable_specs[PROFESORI])

    for pos, subject in enumerate(timetable_specs[MATERII].keys()):
        subject_to_prof_score[subject] /= len(timetable_specs[SALI])
        subject_to_class_score[subject] /= len(timetable_specs[PROFESORI])

        score = subject_to_class_score[subject] + 0.25 * subject_to_prof_score[subject]

        final_scores.append((score, pos, subject))

    final_scores.sort()

    return list(map(lambda t: t[2], final_scores))


def astar(timetable_specs):
    num_states = 1

    min_classroom_size = float('inf')
    for classroom in timetable_specs[SALI]:
        if timetable_specs[SALI][classroom][CAPACITATE] < min_classroom_size:
            min_classroom_size = timetable_specs[SALI][classroom][CAPACITATE]

    subject_order = generate_subject_order(timetable_specs)

    start = generate_initial_timetable(timetable_specs)
    frontier = []
    heappush(frontier, (0, 0, start))

    discovered = {str(start): 0}

    heap_entries_count_priority = 0

    while frontier:
        _, _, node = heappop(frontier)

        if all_covered(node, timetable_specs):
            print ("States generated:", num_states)
            return node

        for n in state_neighbours(node, timetable_specs, subject_order):
            state_key = str(n)

            if state_key not in discovered:
                num_states += 1
                heap_entries_count_priority -= 1
                heappush(frontier, (g(n) + h(n, timetable_specs, min_classroom_size), heap_entries_count_priority, n) )
                discovered[state_key] = g(n)

    return None


def prepare_output(result, timetable_specs):
    del result[ENTRIES_NO]
    del result[PROF_INTERVALS_NO]
    del result[STUDENTS_TO_ASSIGN_PER_SUBJECT]
    del result[WEAK_CONSTRAINTS]

    for day in timetable_specs[ZILE]:
        for interval in timetable_specs[INTERVALE]:
            
            interval = literal_eval(interval)
            for sala in timetable_specs[SALI].keys():

                if sala not in result[day][interval]:
                    result[day][interval][sala] = None

    return result


def check_constraint(solution, constraint):
    return constraint[1](*list(map(lambda a: solution[a], constraint[0])))


def fixed_constraints(solution, constraints):
    fixed = []
    for constraint in constraints:
        is_fixed = True
        for variable in constraint[0]:
            if variable not in solution:
                is_fixed = False
                break
        if is_fixed:
            fixed.append(constraint)
    return fixed


def pcsp_aux(vars, domains, soft_constraints, hard_constraints, solution, cost, unfinished_subjects, prof_intervals, timetable_specs):
    global best_solution
    global best_cost
    global iterations
    global best_iterations

    if best_solution and (iterations - best_iterations) >= CSP_DELTA_ITERATIONS_UNTIL_TIMEOUT:
        return False

    if not unfinished_subjects:
        print("New best: " + str(cost))
        best_solution = copy.deepcopy(solution)
        best_cost = cost
        best_iterations = iterations
        return True

    elif not vars:
        return False
    elif not domains[vars[0]]: 
        return False
    elif cost >= best_cost:
        return False
    else:
        var = vars[0]
        val = domains[var].pop(0)
        iterations += 1

        new_solution = copy.deepcopy(solution)
        new_solution[var] = val

        evaluable_hard_constraints = fixed_constraints(new_solution, hard_constraints)
        evaluable_hard_constraints = list(filter(lambda a: var in a[0], evaluable_hard_constraints))

        hard_cost = len(list(filter(lambda a: not check_constraint(new_solution, a), evaluable_hard_constraints)))

        if hard_cost == 0:
            new_cost = cost
            if val != None:
                # Add new soft constraints to cost
                evaluable_constraints = fixed_constraints(new_solution, soft_constraints)
                evaluable_constraints = list(filter(lambda a: var in a[0], evaluable_constraints))
                new_cost += len(list(filter(lambda a: not check_constraint(new_solution, a), evaluable_constraints)))

            if new_cost < best_cost:
                new_domains = copy.deepcopy(domains)
                new_subjects = copy.deepcopy(unfinished_subjects)
                new_prof_intervals = copy.deepcopy(prof_intervals)

                # Decrease students for the chosen subject
                if val != None:
                    prof_name = val[0]
                    materie = val[1]
                    sala = var[2]

                    new_subjects[materie] -= timetable_specs[SALI][sala][CAPACITATE]

                    # Remove this prof from the same interval
                    for entry in new_domains.keys():
                        if entry[0] == var[0] and entry[1] == var[1]:
                            new_domains[entry] = list(filter(lambda a: a == None or a[0] != prof_name, new_domains[entry]))

                    new_prof_intervals[prof_name] -= 1

                    if new_prof_intervals[prof_name] == 0:
                        # Remove this professor from all domains
                        for entry in new_domains.keys():
                            new_domains[entry] = list(filter(lambda a: a == None or a[0] != prof_name, new_domains[entry]))

                    if new_subjects[materie] <= 0:
                        # Remove it from all domains, since it is not required anymore
                        del new_subjects[materie]

                        filtered_domains = {}
                        for entry, entry_val in new_domains.items():
                            filtered_domains[entry] = list(filter(lambda a: a == None or a[1] != materie, entry_val))
                        
                        new_domains = filtered_domains

                new_vars = vars[1:]
                pcsp_aux(new_vars, new_domains, soft_constraints, hard_constraints, new_solution, new_cost, new_subjects, new_prof_intervals, timetable_specs)

        if best_solution and (iterations - best_iterations) >= CSP_DELTA_ITERATIONS_UNTIL_TIMEOUT:
            return False

        pcsp_aux(vars, domains, soft_constraints, hard_constraints, solution, cost, unfinished_subjects, prof_intervals, timetable_specs)


def compute_vars(timetable_specs):  # [(zi, interval, sala)]
    variables = []
    for zi in timetable_specs[ZILE]:
        for interval in timetable_specs[INTERVALE]:
            for sala in timetable_specs[SALI]:
                variables.append((zi, literal_eval(interval), sala))

    variables.sort(key=lambda a: timetable_specs[SALI][a[2]][CAPACITATE], reverse=True)

    return variables


def compute_domains(variables, timetable_specs):
    domains = {}
    subject_order = generate_subject_order(timetable_specs)

    for variable in variables:
        domains[variable] = []

        for materie in timetable_specs[SALI][variable[2]][MATERII]:
            valid_profs = [prof for prof in timetable_specs[PROFESORI] if materie in timetable_specs[PROFESORI][prof][MATERII]]

            for valid_prof in valid_profs:
                domains[variable].append((valid_prof, materie))

        constrangeri_per_prof = {}
        for prof in timetable_specs[PROFESORI]:
            constrangeri_per_prof[prof] = 0

            for constrangere in timetable_specs[PROFESORI][prof][CONSTRANGERI]:
                    if constrangere[0] != "!":
                        continue

                    if constrangere[1:] == variable[0]:
                        constrangeri_per_prof[prof] += 1
                        continue

                    if "-" in constrangere:
                        parsed_interval = parse_interval(constrangere[1:])

                        if parsed_interval[0] <= variable[1][0] and variable[1][1] <= parsed_interval[1]:
                            constrangeri_per_prof[prof] += 1

        domains[variable].sort(key=lambda a: (subject_order.index(a[1]), constrangeri_per_prof[a[0]]))

        domains[variable] = domains[variable] + [None]

    return domains


def no_same_prof_in_same_interval_constraint(a, b):
    if a == None or b == None:
        return True
    return a[0] != b[0]


def compute_hard_constraints(variables, timetable_specs):
    constraints = []

    for var1 in variables:
        for var2 in variables:
            if var1 == var2:
                continue

            if var1[0] == var2[0] and var1[1] == var2[1]:
                constraints.append(([var1, var2], no_same_prof_in_same_interval_constraint))

    return constraints


def compute_soft_constraints(variables, timetable_specs):  # I'm atomically close to off-ing myself. Unironically.
    soft_constraints = []

    for prof in timetable_specs[PROFESORI]:
        prof_copy = copy.deepcopy(prof)
        for constrangere in timetable_specs[PROFESORI][prof][CONSTRANGERI]:
            if constrangere[0] != "!":
                continue

            if "-" in constrangere:
                parsed_interval = parse_interval(constrangere[1:])

                for left_interval_margin in range(parsed_interval[0], parsed_interval[1], 2):
                    for day in timetable_specs[ZILE]:
                        for sala in timetable_specs[SALI]:
                            variable = (day, (left_interval_margin, left_interval_margin+2), sala)
                            soft_constraints.append(([variable], lambda a, prof_val = prof_copy: a[0] != prof_val))

                continue
            elif "Pauza" in constrangere:
                continue
            else:
                day = constrangere[1:]

                for interval in timetable_specs[INTERVALE]:
                    interval = literal_eval(interval)
                    for sala in timetable_specs[SALI]:
                        variable = (day, interval, sala)
                        soft_constraints.append(([variable], lambda a, prof_val = prof_copy: a[0] != prof_val))
                continue

    return soft_constraints


def prepare_output_pcsp(result, timetable_specs):
    timetable = {}

    for day in timetable_specs[ZILE]:
        timetable[day] = {}

        for interval in timetable_specs[INTERVALE]:
            interval = literal_eval(interval)
            timetable[day][interval] = {}

            for classroom in timetable_specs[SALI]:
                timetable[day][interval][classroom] = None

    for when, who in result.items():
        timetable[when[0]][when[1]][when[2]] = who

    return timetable


def run_pcsp(input_path, timetable_specs):
    global best_solution
    global best_cost
    global iterations
    global best_iterations

    print("Running pcsp.")

    best_iterations = 0
    best_solution = None
    best_cost = float('inf')
    iterations = 0

    students_needed_dict = {}
    for subject, students_needed in timetable_specs[MATERII].items():
        students_needed_dict[subject] = students_needed

    prof_intervals = {}
    for prof in timetable_specs[PROFESORI]:
        prof_intervals[prof] = 7

    variables = compute_vars(timetable_specs)

    domains = compute_domains(variables, timetable_specs)

    hard_constraints = compute_hard_constraints(variables, timetable_specs)
    soft_constraints = compute_soft_constraints(variables, timetable_specs)

    pcsp_aux(variables, copy.deepcopy(domains), soft_constraints, hard_constraints, {}, 0, copy.deepcopy(students_needed_dict), prof_intervals, timetable_specs)

    result = best_solution

    print("Number of iterations:", iterations)

    if result == None:
        print("No solution found")
        return
    
    result = prepare_output_pcsp(result, timetable_specs)
    print(pretty_print_timetable(result, input_path))

    print("Constrangeri soft:", check_optional_constraints(result, timetable_specs))
    print("Constrangeri hard:", check_mandatory_constraints(result, timetable_specs))


def run_a_star(input_path, timetable_specs):
    print("Running a*.")
    result = astar(timetable_specs)

    if (result == None):
        print ("No solution found.")
        return

    print(result[WEAK_CONSTRAINTS])
    result = prepare_output(result, timetable_specs)
    print(pretty_print_timetable(result, input_path))

    print("Constrangeri soft:", check_optional_constraints(result, timetable_specs))
    print("Constrangeri hard:", check_mandatory_constraints(result, timetable_specs))


if __name__ == "__main__":

    if len(sys.argv) != 3:
        print("\npython3 orar.py algorithm input_file_name\n")
        sys.exit(0)

    algorithm = sys.argv[1]
    name = sys.argv[2]

    input_name = f'inputs/{name}.yaml'
    timetable_specs = read_yaml_file(input_name)

    if algorithm == "astar":
        run_a_star(input_name, timetable_specs)
    elif algorithm == "csp":
        run_pcsp(input_name, timetable_specs)
    else:
        print("Unknown algorithm.")
    
    print("End!")
