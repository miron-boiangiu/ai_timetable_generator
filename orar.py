import sys
import json
import os
import copy
import random

from ast import literal_eval
from heapq import heappop, heappush
from check_constraints import *
from utils import *

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


def count_weak_constraints(state, timetable_specs):
    count = 0

    return count


def pick_subject(state, subject_order):

    possible_subjects = [subject for subject in subject_order if state[STUDENTS_TO_ASSIGN_PER_SUBJECT][subject] > 0]
    return possible_subjects[0]


def state_neighbours(state, timetable_specs, subject_order):

    unfinished_subject = pick_subject(state, subject_order)
    valid_profs = [prof for prof in timetable_specs[PROFESORI].keys() if unfinished_subject in timetable_specs[PROFESORI][prof][MATERII]]
    valid_profs = list(filter(lambda prof: state[PROF_INTERVALS_NO][prof] > 0, valid_profs))
    valid_classrooms = [classroom for classroom in timetable_specs[SALI].keys() if unfinished_subject in timetable_specs[SALI][classroom][MATERII]]

    new_states = []

    for day in timetable_specs[ZILE]:
        for interval in state[day]:

            profs_in_interval = [tup[0] for sala, tup in state[day][interval].items()]
            available_profs = [prof for prof in valid_profs if prof not in profs_in_interval]

            for classroom in valid_classrooms:

                if classroom in state[day][interval]:
                    continue

                for prof in available_profs:
                    new_state = copy.deepcopy(state)
                    new_state[ENTRIES_NO] += 1
                    new_state[day][interval][classroom] = (prof, unfinished_subject)
                    new_state[STUDENTS_TO_ASSIGN_PER_SUBJECT][unfinished_subject] -= timetable_specs[SALI][classroom][CAPACITATE]
                    new_state[PROF_INTERVALS_NO][prof] -= 1
                    new_states.append(new_state)

    print("Computed", len(new_states), "neighbours")
    random.shuffle(new_states)
    return new_states


def h(state, timetable_specs, min_classroom_size):
    unfinished_subjects = [tup for tup in state[STUDENTS_TO_ASSIGN_PER_SUBJECT].items() if tup[1] > 0]

    if len(unfinished_subjects) == 0:
        return 0

    leftover_students = sum(map(lambda a: a[1], unfinished_subjects))
    return leftover_students / min_classroom_size


def g(state):
    return state[ENTRIES_NO]


def generate_initial_timetable(timetable_specs):
    timetable = {}

    for day in timetable_specs[ZILE]:
        timetable[day] = {}

        for interval in timetable_specs[INTERVALE]:
            interval = literal_eval(interval)
            timetable[day][interval] = {}

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

        score = 0.5 * subject_to_prof_score[subject] + subject_to_class_score[subject]

        final_scores.append((score, pos, subject))

    final_scores.sort()

    return list(map(lambda t: t[2], final_scores))


def astar(timetable_specs, max_iters = -1):

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

        if max_iters > 0:
            max_iters -= 1
            if max_iters == 0:
                return node

        if all_covered(node, timetable_specs):
            return node

        print("Looking at a node with", node[ENTRIES_NO], "entries")

        for n in state_neighbours(node, timetable_specs, subject_order):
            state_key = str(n)

            if state_key not in discovered:
                heap_entries_count_priority -= 1
                heappush(frontier, (g(n) + h(n, timetable_specs, min_classroom_size), heap_entries_count_priority, n) )
                discovered[state_key] = g(n)

        print("Heap now has", len(frontier), "elements")
        # frontier = frontier[:500]

    return None


def prepare_output(result, timetable_specs):
    del result[ENTRIES_NO]
    del result[PROF_INTERVALS_NO]
    del result[STUDENTS_TO_ASSIGN_PER_SUBJECT]

    for day in timetable_specs[ZILE]:
        for interval in timetable_specs[INTERVALE]:
            
            interval = literal_eval(interval)
            for sala in timetable_specs[SALI].keys():

                if sala not in result[day][interval]:
                    result[day][interval][sala] = None

    return result


def run_a_star(input_file_name, timetable_specs, input_path):
    print("Running a*.")
    result = astar(timetable_specs)
    # print(result)
    print(result[STUDENTS_TO_ASSIGN_PER_SUBJECT])

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

    acces_yaml_attributes(timetable_specs)

    if algorithm == "astar":
        run_a_star(input_name, timetable_specs, input_name)
    else:
        print("Unknown algorithm.")
    
    print("End!")
