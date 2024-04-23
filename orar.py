import sys
import os
import copy
import random

from ast import literal_eval
from heapq import heappop, heappush
from check_constraints import *
from utils import *

# State macros
INTERVAL_POS = 0
PROF_NAME_POS = 1
DAY_POS = 2
CLASSROOM_POS = 3
SUBJECT_POS = 4

# The format of the state is a tuple of tuples, consisting of what entries there are so far:
# (((interval_start, interval_end), "Prof name", "Day", "Classroom", "Subject"), ...)


def all_covered(state, timetable_specs):
    # Considering the state is valid, are all subjects covered?

    subjects = copy.deepcopy(timetable_specs[MATERII])
    classrooms = timetable_specs[SALI]

    for interval, prof_name, day, classroom, subject in state:
        subjects[subject] -= classrooms[classroom][CAPACITATE]

    for subject, capacitate in subjects.items():
        if capacitate > 0:
            return False

    return True


def get_uncovered(state, timetable_specs):
    # Considering the state is valid, are all subjects covered?

    subjects = copy.deepcopy(timetable_specs[MATERII])
    classrooms = timetable_specs[SALI]

    for interval, prof_name, day, classroom, subject in state:
        subjects[subject] -= classrooms[classroom][CAPACITATE]

    unfinished_subjects = []

    for subject, capacitate in subjects.items():
        if capacitate > 0:
            unfinished_subjects.append((subject, capacitate))

    unfinished_subjects.sort(key=lambda a: a[1])
    return unfinished_subjects


def is_valid_state(state, timetable_specs):
    # Are all hard constraints respected?

    number_of_entries = len(state)

    prof_interval_count = {}
    for prof in timetable_specs[PROFESORI].keys():
        prof_interval_count[prof] = 7

    for i in range(number_of_entries):
        
        entry_i = state[i]

        # Can the teacher even teach this?
        if entry_i[SUBJECT_POS] not in timetable_specs[PROFESORI][entry_i[PROF_NAME_POS]][MATERII]:
            return False

        # Is the classroom fit for this subject?
        if entry_i[SUBJECT_POS] not in timetable_specs[SALI][entry_i[CLASSROOM_POS]][MATERII]:
            return False
        
        prof_interval_count[entry_i[PROF_NAME_POS]] -= 1

        for j in range(i + 1, number_of_entries):
            entry_j = state[j]

            #  Is the same professor teaching in the same interval?
            if entry_i[PROF_NAME_POS] == entry_j[PROF_NAME_POS] and entry_i[DAY_POS] == entry_j[DAY_POS] and entry_i[INTERVAL_POS] == entry_j[INTERVAL_POS]:
                return False

            #  Is the same classroom occupied in the same interval?
            if entry_i[CLASSROOM_POS] == entry_j[CLASSROOM_POS] and entry_i[DAY_POS] == entry_j[DAY_POS] and entry_i[INTERVAL_POS] == entry_j[INTERVAL_POS]:
                return False

    for prof_name, interval_count in prof_interval_count.items():
        if interval_count < 0:
            return False

    return True


def count_weak_constraints(state, timetable_specs):
    count = 0

    return count


def state_neighbours(state, timetable_specs):

    unfinished_subject = get_uncovered(state, timetable_specs)[0][0]
    valid_profs = [prof for prof in timetable_specs[PROFESORI].keys() if unfinished_subject in timetable_specs[PROFESORI][prof][MATERII]]
    valid_classrooms = [classroom for classroom in timetable_specs[SALI].keys() if unfinished_subject in timetable_specs[SALI][classroom][MATERII]]

    state = list(state)
    new_entries = [(interval, name, day, classroom, unfinished_subject) for interval in timetable_specs[INTERVALE] for name in valid_profs for day in timetable_specs[ZILE] for classroom in valid_classrooms]
    random.shuffle(new_entries)
    new_states = [state + [entry] for entry in new_entries]
    neighbours = list(filter(lambda a: is_valid_state(a, timetable_specs), new_states))
    for entry in neighbours:
        entry.sort()

    # print("Computed", len(neighbours), "neighbours")
    return map(lambda a: tuple(a), neighbours)


def f(state, timetable_specs, max_classroom_size, min_classroom_size):
    unfinished_subjects = get_uncovered(state, timetable_specs)

    if len(unfinished_subjects) == 0:
        return len(state)

    leftover_students = sum(map(lambda a: a[1], unfinished_subjects))
    return len(state) + (leftover_students / min_classroom_size)


def astar(timetable_specs, max_iters = -1):

    max_classroom_size = 0
    min_classroom_size = float('inf')
    for classroom in timetable_specs[SALI]:
        if timetable_specs[SALI][classroom][CAPACITATE] > max_classroom_size:
            max_classroom_size = timetable_specs[SALI][classroom][CAPACITATE]

        if timetable_specs[SALI][classroom][CAPACITATE] < min_classroom_size:
            min_classroom_size = timetable_specs[SALI][classroom][CAPACITATE]

    start = ()
    frontier = []
    heappush(frontier, (0, start))

    discovered = {start: 0}

    while frontier:
        _, node = heappop(frontier)

        if max_iters > 0:
            max_iters -= 1
            if max_iters == 0:
                return node

        if all_covered(node, timetable_specs):
            return node

        # print("Looking at a node with", len(node), "entries")

        for n in state_neighbours(node, timetable_specs):
            if n not in discovered:  #TODO: Reimplement this
                heappush(frontier, (f(n, timetable_specs, max_classroom_size, min_classroom_size), n ) )
                discovered[n] = discovered[node] + 1

        # print("Heap now has", len(frontier), "elements")
        # print(frontier[0][0])
        # frontier = frontier[:500]

    return None


def convert_timetable_format(timetable, timetable_specs):
    new_timetable = {}
    interval_dict = {}

    for interval in timetable_specs[INTERVALE]:
        interval_dict[literal_eval(interval)] = {}

        for sala in timetable_specs[SALI].keys():
            interval_dict[literal_eval(interval)][sala] = {}

    for zi in timetable_specs[ZILE]:
        new_timetable[zi] = copy.deepcopy(interval_dict)

    for entry in timetable:
        new_timetable[entry[DAY_POS]][literal_eval(entry[INTERVAL_POS])][entry[CLASSROOM_POS]] = (entry[PROF_NAME_POS], entry[SUBJECT_POS])

    return new_timetable

def run_a_star(input_file_name, timetable_specs, input_path):
    print("Running a*.")
    result = astar(timetable_specs, 1000)

    proper_format = convert_timetable_format(result, timetable_specs)
    print(pretty_print_timetable(proper_format, input_path))

    # print("Constrangeri soft:", check_optional_constraints(proper_format, timetable_specs))
    print("Constrangeri hard:", check_mandatory_constraints(proper_format, timetable_specs))

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
