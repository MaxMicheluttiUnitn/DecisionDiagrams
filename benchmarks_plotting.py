"""main and functions to plot the results of the program running on benchmarks"""
import copy
from enum import Enum
import json
import os
from dataclasses import dataclass
# from pprint import pprint
from typing import List, Tuple
import matplotlib.pyplot as plt

TITLE_SIZE = 20
TICK_SIZE = 14
AXES_LABEL_SIZE = 20

plt.rc('font', size=AXES_LABEL_SIZE)
plt.rc('axes', titlesize=TITLE_SIZE)
plt.rc('xtick', labelsize=TICK_SIZE)
plt.rc('ytick', labelsize=TICK_SIZE)


class DataSource(Enum):
    """annotation to keep track of which computation was used"""
    THEORY_BDD = 1
    ABSTRACTION_BDD = 2
    THEORY_SDD = 3
    ABSTRACTION_SDD = 4
    LDD = 5


@dataclass
class Point:
    """a Point that can be plotted"""
    source: DataSource
    computation_time: float
    all_smt_time: float
    dd_time: float
    dd_models: float
    dd_nodes: int
    total_lemmas: int
    fresh_atoms: int
    fresh_atoms_quantification_time: float
    title: str
    timeout: bool


def get_wmi_bench_data(kind: str, source: str) -> List[Point]:
    """gets the computation data from wmi bench"""
    points = []

    # retrieving mutex result
    files = os.listdir(source+"/mutex")
    for filename in files:
        f = open(source+"/mutex/"+filename, encoding="utf8")
        data = json.load(f)
        if len(data) == 0 or data.get("timeout") is not None:
            points.append(Point(DataSource.THEORY_SDD, 0,
                          0, 0, 0, 0, 0, 0, 0, "mutex/"+filename, True))
            continue
        if data.get("All-SAT computation time") is not None:
            allsmttime = data.get("All-SAT computation time")
        else:
            allsmttime = 1000
        if data.get("T-lemmas amount") is not None:
            tlemmas = data["T-lemmas amount"]
        elif data.get("total lemmas") is not None:
            tlemmas = data["total lemmas"]
        else:
            tlemmas = 0
        points.append(Point(DataSource.THEORY_SDD,
                            data["total computation time"],
                            allsmttime,
                            data[kind]["total processing time"],
                            data[kind]["model count"],
                            data[kind]["DD nodes"],
                            tlemmas,
                            data[kind]["fresh T-atoms detected"],
                            data[kind]["fresh T-atoms quantification time"],
                            "mutex/"+filename, False))

    # retrieving xor result
    files = os.listdir(source+"/xor")
    for filename in files:
        f = open(source+"/xor/"+filename, encoding="utf8")
        data = json.load(f)
        if len(data) == 0 or data.get("timeout") is not None:
            points.append(Point(DataSource.THEORY_SDD,
                          0, 0, 0, 0, 0, 0, 0, 0, "xor/"+filename, True))
            continue
        if data.get("All-SAT computation time") is not None:
            allsmttime = data.get("All-SAT computation time")
        else:
            allsmttime = 1000
        if data.get("T-lemmas amount") is not None:
            tlemmas = data["T-lemmas amount"]
        elif data.get("total lemmas") is not None:
            tlemmas = data["total lemmas"]
        else:
            tlemmas = 0
        points.append(Point(DataSource.THEORY_SDD,
                            data["total computation time"],
                            allsmttime,
                            data[kind]["total processing time"],
                            data[kind]["model count"],
                            data[kind]["DD nodes"],
                            tlemmas,
                            data[kind]["fresh T-atoms detected"],
                            data[kind]["fresh T-atoms quantification time"],
                            "xor/"+filename,
                            False))

    return points


def get_ldd_randgen_bench_data(kind: str, source: str) -> List[Point]:
    """gets the computation data from a run on randomly generated LDD benchmark problems"""
    points = []
    files_list: List[str] = []
    for path, _subdirs, files in os.walk(source):
        for name in files:
            files_list.append(os.path.join(path, name))
    for filename in files_list:
        f = open(filename, encoding="utf8")
        data = json.load(f)
        if len(data) == 0 or data.get("timeout") is not None:
            points.append(Point(DataSource.THEORY_BDD, 0, 0, 0, 0, 0, 0, 0, 0, filename.replace(
                source+"/", ''), True))
            continue
        if data.get("All-SMT computation time") is not None:
            allsmttime = data["All-SMT computation time"]
        else:
            # to avoid errors with abstraction DDs
            allsmttime = 0.1
        if data.get("T-lemmas amount") is not None:
            tlemmas = data["T-lemmas amount"]
        elif data.get("total lemmas") is not None:
            tlemmas = data["total lemmas"]
        else:
            tlemmas = 0

        if data.get(kind) is not None:
            if data.get(kind).get("fresh T-atoms detected") is not None:
                fresh_atoms = data[kind]["fresh T-atoms detected"]
            else:
                fresh_atoms = 0
        else:
            fresh_atoms = 0

        if data.get(kind) is not None:
            if data.get(kind).get("fresh T-atoms quantification time") is not None:
                fresh_atoms_quant_time = data[kind]["fresh T-atoms quantification time"]
            else:
                fresh_atoms_quant_time = 0
        else:
            fresh_atoms_quant_time = 0
        
        points.append(Point(DataSource.THEORY_BDD,
                            data["total computation time"],
                            allsmttime,
                            data[kind]["total DD computation time"],
                            data[kind]["DD models"],
                            data[kind]["DD nodes"],
                            tlemmas,
                            fresh_atoms,
                            fresh_atoms_quant_time,
                            filename.replace(source+"/", ''), False))
    return points


def get_randgen_bench_data(kind: str, source: str) -> List[Point]:
    """gets the computation data from a run on randomly generated benchmark problems"""
    points = []
    files_list: List[str] = []
    for path, _subdirs, files in os.walk(source):
        for name in files:
            files_list.append(os.path.join(path, name))
    for filename in files_list:
        f = open(filename, encoding="utf8")
        data = json.load(f)
        if len(data) == 0 or data.get("timeout") is not None:
            points.append(Point(DataSource.THEORY_BDD, 0, 0, 0, 0, 0, 0, 0, 0, filename.replace(
                source+"/", ''), True))
            continue
        if data.get("All-SMT computation time") is not None:
            allsmttime = data["All-SMT computation time"]
        else:
            allsmttime = 0.1
        if data.get("T-lemmas amount") is not None:
            tlemmas = data["T-lemmas amount"]
        elif data.get("total lemmas") is not None:
            tlemmas = data["total lemmas"]
        else:
            tlemmas = 0
        points.append(Point(DataSource.THEORY_BDD,
                            data["total computation time"],
                            allsmttime,
                            data[kind]["total DD computation time"],
                            data[kind]["DD models"],
                            data[kind]["DD nodes"],
                            tlemmas,
                            data[kind]["fresh T-atoms detected"],
                            data[kind]["fresh T-atoms quantification time"],
                            filename.replace(source+"/", ''), False))
    return points


def get_smtlib_bench_data(kind: str, source: str) -> List[Point]:
    """gets the computation data from a run on smtlib benchmark problems"""
    points = []
    files_list: List[str] = []
    for path, _subdirs, files in os.walk(source):
        for name in files:
            files_list.append(os.path.join(path, name))
    for filename in files_list:
        if filename.count("smt2") > 0:
            continue
        f = open(filename, encoding="utf8")
        data = json.load(f)
        if len(data) == 0 or data.get("timeout") is not None:
            points.append(Point(DataSource.THEORY_BDD, 0, 0, 0, 0, 0, 0, 0, 0, filename.replace(
                source+"/", ''), True))
            continue
        if data.get("All-SMT computation time") is not None:
            allsmttime = data["All-SMT computation time"]
        else:
            allsmttime = 3600

        if data.get(kind) is not None:
            if data.get(kind).get("total DD computation time") is not None:
                ddtime = data[kind]["total DD computation time"]
            elif data.get(kind).get("total processing time") is not None:
                ddtime = data[kind]["total processing time"]
            else:
                ddtime = 3600
        else:
            ddtime = 3600
            ddmodels = None

        if data.get("T-lemmas amount") is not None:
            tlemmas = data["T-lemmas amount"]
        elif data.get("total lemmas") is not None:
            tlemmas = data["total lemmas"]
        else:
            tlemmas = 0

        if data.get(kind) is not None:
            if data.get(kind).get("DD models") is not None:
                ddmodels = data[kind]["DD models"]
            else:
                ddmodels = None

        if data.get(kind) is not None:
            if data.get(kind).get("DD nodes") is not None:
                ddnodes = data[kind]["DD nodes"]
            else:
                ddnodes = 0
        else:
            ddnodes = 0

        if data.get(kind) is not None:
            if data.get(kind).get("fresh T-atoms detected") is not None:
                fresh_atoms = data[kind]["fresh T-atoms detected"]
            else:
                fresh_atoms = 0
        else:
            fresh_atoms = 0

        if data.get(kind) is not None:
            if data.get(kind).get("fresh T-atoms quantification time") is not None:
                fresh_atoms_quant_time = data[kind]["fresh T-atoms quantification time"]
            else:
                fresh_atoms_quant_time = 0
        else:
            fresh_atoms_quant_time = 0

        points.append(Point(DataSource.THEORY_BDD,
                            data["total computation time"],
                            allsmttime,
                            ddtime,
                            ddmodels,
                            ddnodes,
                            tlemmas,
                            fresh_atoms,
                            fresh_atoms_quant_time,
                            filename.replace(source+"/", ''), False))
    return points


def get_time_points(
        theory_points: List[Point],
        abstraction_points: List[Point]) -> Tuple[List[float], List[float], int]:
    """translate data into plottable points comparing time"""
    theory_points = copy.deepcopy(theory_points)
    abstraction_points = copy.deepcopy(abstraction_points)

    theory_list = []
    abstraction_list = []
    max_theory = theory_points[0].computation_time
    max_abstraction = abstraction_points[0].computation_time

    for t_p in theory_points:
        if t_p.computation_time > max_theory:
            max_theory = t_p.computation_time
    for a_p in abstraction_points:
        if a_p.computation_time > max_abstraction:
            max_abstraction = a_p.computation_time

    edge = max(max_theory, max_abstraction) * 10

    for t_p in theory_points:
        if t_p.timeout:
            t_p.computation_time = edge
    for a_p in abstraction_points:
        if a_p.timeout:
            a_p.computation_time = edge

    for t_p in theory_points:
        for a_p in abstraction_points:
            if t_p.title == a_p.title:
                theory_list.append(t_p.computation_time)
                abstraction_list.append(a_p.computation_time)
                break
    return (theory_list, abstraction_list, edge)


def get_allsmt_time_points(
        theory_points: List[Point],
        abstraction_points: List[Point]) -> Tuple[List[float], List[float], int]:
    """translate data into plottable points comparing all SMT time"""
    theory_points = copy.deepcopy(theory_points)
    abstraction_points = copy.deepcopy(abstraction_points)

    theory_list = []
    abstraction_list = []
    max_theory = theory_points[0].all_smt_time
    max_abstraction = abstraction_points[0].all_smt_time

    for t_p in theory_points:
        if t_p.all_smt_time > max_theory:
            max_theory = t_p.all_smt_time
    for a_p in abstraction_points:
        if a_p.all_smt_time > max_abstraction:
            max_abstraction = a_p.all_smt_time

    edge = max(max_theory, max_abstraction) * 10

    for t_p in theory_points:
        if t_p.timeout:
            t_p.all_smt_time = edge
    for a_p in abstraction_points:
        if a_p.timeout:
            a_p.all_smt_time = edge

    for t_p in theory_points:
        for a_p in abstraction_points:
            if t_p.title == a_p.title:
                theory_list.append(t_p.all_smt_time)
                abstraction_list.append(a_p.all_smt_time)
                break
    return (theory_list, abstraction_list, edge)


def get_dd_time_points(
        theory_points: List[Point],
        abstraction_points: List[Point]) -> Tuple[List[float], List[float], int]:
    """translate data into plottable points comparing all SMT time"""
    theory_points = copy.deepcopy(theory_points)
    abstraction_points = copy.deepcopy(abstraction_points)

    theory_list = []
    abstraction_list = []
    max_theory = theory_points[0].dd_time
    max_abstraction = abstraction_points[0].dd_time

    for t_p in theory_points:
        if t_p.dd_time > max_theory:
            max_theory = t_p.dd_time
    for a_p in abstraction_points:
        if a_p.dd_time > max_abstraction:
            max_abstraction = a_p.dd_time

    edge = max(max_theory, max_abstraction) * 10

    for t_p in theory_points:
        if t_p.timeout:
            t_p.dd_time = edge
    for a_p in abstraction_points:
        if a_p.timeout:
            a_p.dd_time = edge

    for t_p in theory_points:
        for a_p in abstraction_points:
            if t_p.title == a_p.title:
                theory_list.append(t_p.dd_time)
                abstraction_list.append(a_p.dd_time)
                break
    return (theory_list, abstraction_list, edge)


def get_lemmas_points(
        theory_points: List[Point],
        abstraction_points: List[Point]) -> Tuple[List[float], List[float], int]:
    """translate data into plottable points comparing DD size in nodes"""
    theory_points = copy.deepcopy(theory_points)
    abstraction_points = copy.deepcopy(abstraction_points)

    theory_list = []
    abstraction_list = []
    max_theory = theory_points[0].total_lemmas
    max_abstraction = abstraction_points[0].total_lemmas

    for t_p in theory_points:
        if t_p.total_lemmas > max_theory:
            max_theory = t_p.total_lemmas
    for a_p in abstraction_points:
        if a_p.total_lemmas > max_abstraction:
            max_abstraction = a_p.total_lemmas

    edge = max(max_theory, max_abstraction) * 2

    for t_p in theory_points:
        if t_p.timeout:
            t_p.dd_nodes = edge
    for a_p in abstraction_points:
        if a_p.timeout:
            a_p.dd_nodes = edge

    for t_p in theory_points:
        for a_p in abstraction_points:
            if t_p.title == a_p.title and not t_p.timeout and not a_p.timeout:
                theory_list.append(t_p.total_lemmas)
                abstraction_list.append(a_p.total_lemmas)
                break
    return (theory_list, abstraction_list, edge)


def get_nodes_points(
        theory_points: List[Point],
        abstraction_points: List[Point]) -> Tuple[List[float], List[float], int]:
    """translate data into plottable points comparing DD size in nodes"""
    theory_points = copy.deepcopy(theory_points)
    abstraction_points = copy.deepcopy(abstraction_points)

    theory_list = []
    abstraction_list = []
    max_theory = theory_points[0].dd_nodes
    max_abstraction = abstraction_points[0].dd_nodes

    for t_p in theory_points:
        if t_p.dd_nodes > max_theory:
            max_theory = t_p.dd_nodes
    for a_p in abstraction_points:
        if a_p.dd_nodes > max_abstraction:
            max_abstraction = a_p.dd_nodes

    edge = max(max_theory, max_abstraction) * 2

    for t_p in theory_points:
        if t_p.timeout:
            t_p.dd_nodes = edge
    for a_p in abstraction_points:
        if a_p.timeout:
            a_p.dd_nodes = edge

    # count11 = 0
    for t_p in theory_points:
        for a_p in abstraction_points:
            if t_p.title == a_p.title and not t_p.timeout and not a_p.timeout:
                # if t_p.dd_nodes == 1 and a_p.dd_nodes == 1:
                #     count11 += 1
                theory_list.append(t_p.dd_nodes)
                abstraction_list.append(a_p.dd_nodes)
                break
    # print("Count 1 1", count11)
    return (theory_list, abstraction_list, edge)

def get_dd_fresh_atoms_points(
        theory_points: List[Point],
        abstraction_points: List[Point]) -> Tuple[List[float], List[float], int]:
    """translate data into plottable points comparing amount of fresh T-atoms"""
    theory_list = []
    abstraction_list = []
    max_theory = theory_points[0].fresh_atoms
    max_abstraction = abstraction_points[0].fresh_atoms

    theory_points = copy.deepcopy(theory_points)
    abstraction_points = copy.deepcopy(abstraction_points)

    for t_p in theory_points:
        if t_p.fresh_atoms is not None and (max_theory is None or t_p.fresh_atoms > max_theory):
            max_theory = t_p.fresh_atoms
    for a_p in abstraction_points:
        if a_p.fresh_atoms is not None and (max_abstraction is None or a_p.fresh_atoms > max_abstraction):
            max_abstraction = a_p.fresh_atoms
    if max_abstraction is None or max_theory is None:
        raise Exception("Un-plottable data provided!!!")

    edge = max(max_theory, max_abstraction) * 10

    # for t_p in theory_points:
    #     if t_p.timeout:
    #         t_p.fresh_atoms = edge
    # for a_p in abstraction_points:
    #     if a_p.timeout:
    #         a_p.fresh_atoms = edge

    for t_p in theory_points:
        for a_p in abstraction_points:
            if t_p.title == a_p.title and not t_p.timeout and not a_p.timeout:
                #print(t_p.fresh_atoms_quantification_time,a_p.fresh_atoms_quantification_time)
                theory_list.append(t_p.fresh_atoms)
                abstraction_list.append(a_p.fresh_atoms)
                break
    return (theory_list, abstraction_list, edge)

def get_dd_models_points(
        theory_points: List[Point],
        abstraction_points: List[Point]) -> Tuple[List[float], List[float], int]:
    """translate data into plottable points comparing DD size in nodes"""
    theory_list = []
    abstraction_list = []
    max_theory = theory_points[0].dd_models
    max_abstraction = abstraction_points[0].dd_models

    theory_points = copy.deepcopy(theory_points)
    abstraction_points = copy.deepcopy(abstraction_points)

    for t_p in theory_points:
        if t_p.dd_models is not None and (max_theory is None or t_p.dd_models > max_theory):
            max_theory = t_p.dd_models
    for a_p in abstraction_points:
        if a_p.dd_models is not None and (max_abstraction is None or a_p.dd_models > max_abstraction):
            max_abstraction = a_p.dd_models

    if max_abstraction is None or max_theory is None:
        raise Exception("Un-plottable data provided!!!")

    edge = max(max_theory, max_abstraction) * 10

    for t_p in theory_points:
        if t_p.timeout:
            t_p.dd_models = edge
    for a_p in abstraction_points:
        if a_p.timeout:
            a_p.dd_models = edge

    # count11 = 0
    for t_p in theory_points:
        for a_p in abstraction_points:
            if t_p.title == a_p.title and t_p.dd_models is not None and a_p.dd_models is not None and not t_p.timeout and not a_p.timeout:
                # if a_p.dd_models < t_p.dd_models:
                #     print(a_p.title)
                # if t_p.dd_nodes == 1 and a_p.dd_nodes == 1:
                #     count11 += 1
                # if t_p.dd_models > 10**30:
                #     print(t_p.title)
                # if a_p.dd_models > 10**30:
                #     print(a_p.title)
                # if(a_p.dd_models > 0):
                #     print(1-t_p.dd_models/a_p.dd_models)
                # else:
                #     print(t_p.dd_models, a_p.dd_models)
                #     print(t_p.title)
                theory_list.append(t_p.dd_models)
                abstraction_list.append(a_p.dd_models)
                break
    # print("Count 1 1", count11)
    return (theory_list, abstraction_list, edge)


def build_graphs(time_points, size_points, x_label: str, y_label: str) -> None:
    """builds and displays graphs"""
    build_time_graph(time_points, x_label, y_label)
    build_size_graph(size_points, x_label, y_label)


def build_time_graph(time_points, x_label: str, y_label: str, file: str | None = None) -> None:
    """builds and displays the time graph"""

    plt.scatter(time_points[0], time_points[1], marker='x')
    plt.xlabel(x_label)
    plt.ylabel(y_label)
    # plt.title("Computation Time")
    ax = plt.gca()
    ax.set_yscale('log')
    ax.set_xscale('log')
    ax.set_aspect('equal', adjustable='box')
    diag_line, = ax.plot(ax.get_xlim(), ax.get_ylim(), ls=":", c=".3")

    multiplier = 0.001
    while multiplier < time_points[2]:
        plt.plot([0.0001, time_points[2]], [multiplier, time_points[2]
                 * multiplier*10000], 'r-', ls=":", c=".3", alpha=0.2)
        plt.plot([multiplier, time_points[2]*multiplier*10000],
                 [0.0001, time_points[2]], 'r-', ls=":", c=".3", alpha=0.2)
        multiplier = multiplier*10

    def on_change_time(_axes):
        x_lims = ax.get_xlim()
        y_lims = ax.get_ylim()
        diag_line.set_data(x_lims, y_lims)
    ax.callbacks.connect('xlim_changed', on_change_time)
    ax.callbacks.connect('ylim_changed', on_change_time)
    plt.axvline(x=time_points[2], ls="--", c=".3")
    plt.axhline(y=time_points[2], ls="--", c=".3")
    plt.xlim((0.0001, 10*time_points[2]))
    plt.ylim((0.0001, 10*time_points[2]))
    # plt.axis('square')

    if file is not None:
        plt.savefig(file, bbox_inches='tight')
    plt.show()


def build_size_graph(size_points, x_label: str, y_label: str, file: str | None = None) -> None:
    """builds and shows the size graph"""
    plt.scatter(size_points[0], size_points[1], marker='x')
    plt.xlabel(x_label)
    plt.ylabel(y_label)
    # plt.title("DD size in nodes")
    ax = plt.gca()
    ax.set_yscale('log')
    ax.set_xscale('log')
    ax.set_aspect('equal', adjustable='box')
    diag_line, = ax.plot(ax.get_xlim(), ax.get_ylim(), ls=":", c=".3")

    multiplier = 10
    while multiplier < size_points[2]:
        plt.plot([1, size_points[2]], [multiplier, size_points[2]
                 * multiplier], 'r-', ls=":", c=".3", alpha=0.2)
        plt.plot([multiplier, size_points[2]*multiplier],
                 [1, size_points[2]], 'r-', ls=":", c=".3", alpha=0.2)
        multiplier = multiplier*10

    def on_change(_axes):
        x_lims = ax.get_xlim()
        y_lims = ax.get_ylim()
        diag_line.set_data(x_lims, y_lims)
    ax.callbacks.connect('xlim_changed', on_change)
    ax.callbacks.connect('ylim_changed', on_change)
    # plt.axis('square')
    # plt.axvline(x=size_points[2], ls="--", c=".3")
    # plt.axhline(y=size_points[2], ls="--", c=".3")
    plt.xlim((1, size_points[2]))
    plt.ylim((1, size_points[2]))

    if file is not None:
        plt.savefig(file, bbox_inches='tight')
    plt.show()


def build_models_graph(points, x_label: str, y_label: str, file: str | None = None) -> None:
    """builds and shows the model count graph"""
    plt.scatter(points[0], points[1], marker='x')
    plt.xlabel(x_label)
    plt.ylabel(y_label)

    # plt.title("DD amount of models")
    ax = plt.gca()
    ax.set_yscale('log')
    ax.set_xscale('log')
    ax.set_aspect('equal', adjustable='box')
    diag_line, = ax.plot(ax.get_xlim(), ax.get_ylim(), ls=":", c=".3")

    multiplier = 1000
    while multiplier < points[2]:
        plt.plot([1, points[2]], [multiplier, points[2]*multiplier],
                 'r-', ls=":", c=".3", alpha=0.2)
        plt.plot([multiplier, points[2]*multiplier],
                 [1, points[2]], 'r-', ls=":", c=".3", alpha=0.2)
        multiplier = multiplier*1000

    def on_change(_axes):
        x_lims = ax.get_xlim()
        y_lims = ax.get_ylim()
        diag_line.set_data(x_lims, y_lims)
    ax.callbacks.connect('xlim_changed', on_change)
    ax.callbacks.connect('ylim_changed', on_change)
    # plt.axis('square')
    # plt.axvline(x=points[2], ls="--", c=".3")
    # plt.axhline(y=points[2], ls="--", c=".3")
    plt.xlim((1, points[2]*10))
    plt.ylim((1, points[2]*10))

    if file is not None:
        plt.savefig(file, bbox_inches='tight')
    plt.show()


def build_lemmas_graph(points, x_label: str, y_label: str, file: str | None = None) -> None:
    """builds and shows the model count graph"""
    plt.scatter(points[0], points[1], marker='x')
    plt.xlabel(x_label)
    plt.ylabel(y_label)

    # plt.title("DD amount of models")
    ax = plt.gca()
    ax.set_yscale('log')
    ax.set_xscale('log')
    ax.set_aspect('equal', adjustable='box')
    diag_line, = ax.plot(ax.get_xlim(), ax.get_ylim(), ls=":", c=".3")

    multiplier = 1000
    while multiplier < points[2]:
        plt.plot([1, points[2]], [multiplier, points[2]*multiplier],
                 'r-', ls=":", c=".3", alpha=0.2)
        plt.plot([multiplier, points[2]*multiplier],
                 [1, points[2]], 'r-', ls=":", c=".3", alpha=0.2)
        multiplier = multiplier*1000

    def on_change(_axes):
        x_lims = ax.get_xlim()
        y_lims = ax.get_ylim()
        diag_line.set_data(x_lims, y_lims)
    ax.callbacks.connect('xlim_changed', on_change)
    ax.callbacks.connect('ylim_changed', on_change)
    # plt.axis('square')
    # plt.axvline(x=points[2], ls="--", c=".3")
    # plt.axhline(y=points[2], ls="--", c=".3")
    plt.xlim((1, points[2]*10))
    plt.ylim((1, points[2]*10))

    if file is not None:
        plt.savefig(file, bbox_inches='tight')
    plt.show()


def main() -> None:
    """main function"""
    # --------------------------------------------------------------
    # WMI

    # wmi_bdds_points = get_wmi_bench_data(
    #     "BDD", "benchmarks/wmi/output")
    # wmi_abstraction_bdd_points = get_wmi_bench_data(
    #     "BDD", "benchmarks/wmi/output_abstraction")
    # wmi_sdds_points = get_wmi_bench_data(
    #     "SDD", "benchmarks/wmi/output_sdd")
    # wmi_abstraction_sdd_points = get_wmi_bench_data(
    #     "SDD", "benchmarks/wmi/output_abstraction_sdd")

    # print("WMI BDD graphs")
    # time_points = get_time_points(
    #     wmi_bdds_points, wmi_abstraction_bdd_points)
    # size_points = get_nodes_points(
    #     wmi_bdds_points, wmi_abstraction_bdd_points)
    # models_points = get_dd_models_points(
    #     wmi_bdds_points, wmi_abstraction_bdd_points)
    # build_time_graph(time_points, "T-OBDD", "Abs. BDD",
    #                  "plots/wmi/abstr_bdd_vs_tbdd_time.pdf")
    # build_size_graph(size_points, "T-OBDD", "Abs. BDD",
    #                  "plots/wmi/abstr_bdd_vs_tbdd_size.pdf")
    # build_models_graph(models_points, "T-OBDD", "Abs. BDD",
    #                    "plots/wmi/abstr_bdd_vs_tbdd_models.pdf")

    # print("WMI SDD graphs")
    # time_points = get_time_points(
    #     wmi_sdds_points, wmi_abstraction_sdd_points)
    # size_points = get_nodes_points(
    #     wmi_sdds_points, wmi_abstraction_sdd_points)
    # build_time_graph(time_points, "T-SDD", "Abs. SDD",
    #                  "plots/wmi/abstr_sdd_vs_tsdd_time.pdf")
    # build_size_graph(size_points, "T-SDD", "Abs. SDD",
    #                  "plots/wmi/abstr_sdd_vs_tsdd_size.pdf")

    # --------------------------------------------------------------
    # LDD RANDGEN

    # ldd_randgen_ldds_points = get_ldd_randgen_bench_data(
    #     "LDD", "benchmarks/ldd_randgen/output_ldd")
    # print(len(ldd_randgen_ldds_points))
    # print("Timeouts of LDDs on LDD randgen: ", len(
    #     list(filter(lambda x: x.timeout, ldd_randgen_ldds_points))))
    # ldd_randgen_bdds_points = get_ldd_randgen_bench_data(
    #     "T-BDD", "benchmarks/ldd_randgen/output")
    # print("Timeouts of T-BDDs on LDD randgen: ",
    #       len(list(filter(lambda x: x.timeout, ldd_randgen_bdds_points))))
    # ldd_randgen_abstraction_bdd_points = get_ldd_randgen_bench_data(
    #     "Abstraction BDD", "benchmarks/ldd_randgen/output_abstraction")
    # print("Timeouts of Abs-BDDs on LDD randgen: ",
    #       len(list(filter(lambda x: x.timeout, ldd_randgen_abstraction_bdd_points))))
    # ldd_randgen_sdds_points = get_ldd_randgen_bench_data(
    #     "T-SDD", "benchmarks/ldd_randgen/output_sdd")
    # print("Timeouts of T-SDDs on LDD randgen: ",
    #       len(list(filter(lambda x: x.timeout, ldd_randgen_sdds_points))))
    # ldd_randgen_abstraction_sdd_points = get_ldd_randgen_bench_data(
    #     "Abstraction SDD", "benchmarks/ldd_randgen/output_abstraction_sdd")
    # print("Timeouts of Abs-SDDs on LDD randgen: ",
    #       len(list(filter(lambda x: x.timeout, ldd_randgen_abstraction_sdd_points))))
    # # ldd_randgen_bdds_newgen_points = get_ldd_randgen_bench_data(
    # #     "T-BDD", "benchmarks/ldd_randgen/output_newddgen")
    # ldd_randgen_bdds_points_noeqsplit = get_ldd_randgen_bench_data(
    #     "T-BDD", "benchmarks/ldd_randgen/output")
    # print("Timeouts of T-BDDs on LDD randgen (no eq split): ",
    #       len(list(filter(lambda x: x.timeout, ldd_randgen_bdds_points_noeqsplit))))

    # print("LDD randgen LDD vs BDD graphs")
    # time_points = get_time_points(
    #     ldd_randgen_bdds_points, ldd_randgen_ldds_points)
    # size_points = get_nodes_points(
    #     ldd_randgen_bdds_points, ldd_randgen_ldds_points)
    # models_points = get_dd_models_points(
    #     ldd_randgen_bdds_points, ldd_randgen_ldds_points)
    # build_time_graph(time_points, "T-OBDD", "LDD",
    #                  "plots/ldd_randgen/ldd_vs_tbdd_time.pdf")
    # build_size_graph(size_points, "T-OBDD", "LDD",
    #                  "plots/ldd_randgen/ldd_vs_tbdd_size.pdf")
    # build_models_graph(models_points, "T-OBDD", "LDD",
    #                    "plots/ldd_randgen/ldd_vs_tbdd_models.pdf")

    # print("LDD randgen BDD no eq graphs")
    # time_points = get_time_points(
    #     ldd_randgen_bdds_points, ldd_randgen_bdds_points_noeqsplit)
    # size_points = get_nodes_points(
    #     ldd_randgen_bdds_points, ldd_randgen_bdds_points_noeqsplit)
    # models_points = get_dd_models_points(
    #     ldd_randgen_bdds_points, ldd_randgen_bdds_points_noeqsplit)
    # build_time_graph(time_points, "NO Opt", "Opt")
    # build_size_graph(size_points, "NO Opt", "Opt")
    # build_models_graph(models_points, "NO Opt", "Opt")

    # print("LDD randgen BDD graphs")
    # time_points = get_time_points(
    #     ldd_randgen_bdds_points, ldd_randgen_abstraction_bdd_points)
    # size_points = get_nodes_points(
    #     ldd_randgen_bdds_points, ldd_randgen_abstraction_bdd_points)
    # models_points = get_dd_models_points(
    #     ldd_randgen_bdds_points, ldd_randgen_abstraction_bdd_points)
    # build_time_graph(time_points, "T-OBDD", "Abs. BDD",
    #                  "plots/ldd_randgen/abstr_bdd_vs_tbdd_time.pdf")
    # build_size_graph(size_points, "T-OBDD", "Abs. BDD",
    #                  "plots/ldd_randgen/abstr_bdd_vs_tbdd_size.pdf")
    # build_models_graph(models_points, "T-OBDD", "Abs. BDD",
    #                    "plots/ldd_randgen/abstr_bdd_vs_tbdd_models.pdf")

    # print("LDD randgen SDD graphs")
    # time_points = get_time_points(
    #     ldd_randgen_sdds_points, ldd_randgen_abstraction_sdd_points)
    # size_points = get_nodes_points(
    #     ldd_randgen_sdds_points, ldd_randgen_abstraction_sdd_points)
    # build_time_graph(time_points, "T-SDD", "Abs. SDD",
    #                  "plots/ldd_randgen/abstr_sdd_vs_tsdd_time.pdf")
    # build_size_graph(size_points, "T-SDD", "Abs. SDD",
    #                  "plots/ldd_randgen/abstr_sdd_vs_tsdd_size.pdf")

    # print("LDD randgen DD gen graphs")
    # time_points = get_dd_time_points(
    #     ldd_randgen_bdds_points, ldd_randgen_bdds_newgen_points)
    # size_points = get_nodes_points(
    #     ldd_randgen_bdds_points, ldd_randgen_bdds_newgen_points)
    # models_points = get_dd_models_points(
    #     ldd_randgen_bdds_points, ldd_randgen_bdds_newgen_points)
    # build_time_graph(time_points, "Old DD", "New DD",
    #                  "plots/ldd_randgen/old_vs_new_dd_time.pdf")
    # build_size_graph(size_points, "Old DD", "New DD",
    #                  "plots/ldd_randgen/old_vs_new_dd_size.pdf")
    # build_models_graph(models_points, "Old DD", "New DD",
    #                    "plots/ldd_randgen/old_vs_new_dd_models.pdf")

    # --------------------------------------------------------------
    # RANDGEN

    # randgen_bdds_points = get_randgen_bench_data(
    #     "T-BDD", "benchmarks/randgen/output_tsetsin")
    # print(len(randgen_bdds_points))
    # print("Timeouts of T-BDDs on randgen: ",
    #       len(list(filter(lambda x: x.timeout, randgen_bdds_points))))
    # randgen_abstraction_bdd_points = get_randgen_bench_data(
    #     "Abstraction BDD", "benchmarks/randgen/output_abstraction")
    # print("Timeouts of Abs-BDDs on randgen: ",
    #       len(list(filter(lambda x: x.timeout, randgen_abstraction_bdd_points))))
    # randgen_sdds_points = get_randgen_bench_data(
    #     "T-SDD", "benchmarks/randgen/output_sdd")
    # print("Timeouts of T-SDDs on randgen: ",
    #       len(list(filter(lambda x: x.timeout, randgen_sdds_points))))
    # randgen_abstraction_sdd_points = get_randgen_bench_data(
    #     "Abstraction SDD", "benchmarks/randgen/output_abstraction_sdd")
    # print("Timeouts of Abs-SDDs on randgen: ",
    #       len(list(filter(lambda x: x.timeout, randgen_abstraction_sdd_points))))
    # randgen_no_eqsplit_points = get_randgen_bench_data(
    #     "T-BDD", "benchmarks/randgen/output_noeqsplit")
    # print("Timeouts of T-OBDDs on randgen no eq split: ",
    #       len(list(filter(lambda x: x.timeout, randgen_no_eqsplit_points))))

    # print("randgen BDD graphs")
    # time_points = get_time_points(
    #     randgen_bdds_points, randgen_abstraction_bdd_points)
    # size_points = get_nodes_points(
    #     randgen_bdds_points, randgen_abstraction_bdd_points)
    # models_points = get_dd_models_points(
    #     randgen_bdds_points, randgen_abstraction_bdd_points)
    # build_time_graph(time_points, "T-OBDD", "Abs. BDD",
    #                  "plots/randgen/abstr_bdd_vs_tbdd_time.pdf")
    # build_size_graph(size_points, "T-OBDD", "Abs. BDD",
    #                  "plots/randgen/abstr_bdd_vs_tbdd_size.pdf")
    # build_models_graph(models_points, "T-BDD", "Abs. BDD",
    #                    "plots/randgen/abstr_bdd_vs_tbdd_models.pdf")

    # print("randgen BDD graphs")
    # time_points = get_time_points(
    #     randgen_bdds_points, randgen_no_eqsplit_points)
    # size_points = get_nodes_points(
    #     randgen_bdds_points, randgen_no_eqsplit_points)
    # models_points = get_dd_models_points(
    #     randgen_bdds_points, randgen_no_eqsplit_points)
    # allsmt_points = get_allsmt_time_points(
    #     randgen_bdds_points, randgen_no_eqsplit_points)
    # build_time_graph(time_points, "No opt", "Opt")
    # build_size_graph(size_points, "No opt", "Opt")
    # build_models_graph(models_points, "No opt", "Opt")
    # build_time_graph(allsmt_points, "No opt", "Opt")

    # print("randgen SDD graphs")
    # time_points = get_time_points(
    #     randgen_sdds_points, randgen_abstraction_sdd_points)
    # size_points = get_nodes_points(
    #     randgen_sdds_points, randgen_abstraction_sdd_points)
    # build_time_graph(time_points, "T-SDD", "Abs. SDD",
    #                  "plots/randgen/abstr_sdd_vs_tsdd_time.pdf")
    # build_size_graph(size_points, "T-SDD", "Abs. SDD",
    #                  "plots/randgen/abstr_sdd_vs_tsdd_size.pdf")

    # --------------------------------------------------------------
    # SMTLIB QF RDL

    qfrdl_ldds_points = get_smtlib_bench_data(
        "LDD", "benchmarks/smtlib/output_ldd/non-incremental/QF_RDL")
    print(len(qfrdl_ldds_points))
    print("Timeouts of LDDs on smtlib QF RDL: ", len(
        list(filter(lambda x: x.timeout, qfrdl_ldds_points))))
    qfrdl_bdds_points = get_smtlib_bench_data(
        "T-BDD", "benchmarks/smtlib/output_bdd/non-incremental/QF_RDL")
    print("Timeouts of T-BDDs on smtlib QF RDL: ",
          len(list(filter(lambda x: x.timeout, qfrdl_bdds_points))))
    qfrdl_abstraction_bdd_points = get_smtlib_bench_data(
        "Abstraction BDD", "benchmarks/smtlib/output_abstraction_bdd/non-incremental/QF_RDL")
    print("Timeouts of Abs-BDDs on smtlib QF RDL: ",
          len(list(filter(lambda x: x.timeout, qfrdl_abstraction_bdd_points))))
    qfrdl_sdds_points = get_smtlib_bench_data(
        "T-SDD", "benchmarks/smtlib/output_sdd/non-incremental/QF_RDL")
    print("Timeouts of T-SDDs on smtlib QF RDL: ",
          len(list(filter(lambda x: x.timeout, qfrdl_sdds_points))))
    qfrdl_abstraction_sdd_points = get_smtlib_bench_data(
        "Abstraction SDD", "benchmarks/smtlib/output_abstraction_sdd/non-incremental/QF_RDL")
    print("Timeouts of Abs-SDDs on smtlib QF RDL: ",
          len(list(filter(lambda x: x.timeout, qfrdl_abstraction_sdd_points))))
    qfrdl_bdds_noeqsplit_points = get_smtlib_bench_data(
        "T-BDD", "benchmarks/smtlib/output_bdd_noeqsplit/non-incremental/QF_RDL")
    print("Timeouts of T-BDDs no eq split on smtlib QF RDL: ",
          len(list(filter(lambda x: x.timeout, qfrdl_bdds_noeqsplit_points))))
    # qfrdl_tmp = get_smtlib_bench_data("", "benchmarks/smtlib/tmp/non-incremental/QF_RDL")
    # qfrdl_tmp_noeqsplit = get_smtlib_bench_data("", "benchmarks/smtlib/tmp_noeqsplit/non-incremental/QF_RDL")

    # print("QF RDL LDD vs BDD graphs")
    # time_points = get_time_points(
    #     qfrdl_bdds_points, qfrdl_ldds_points)
    # size_points = get_nodes_points(
    #     qfrdl_bdds_points, qfrdl_ldds_points)
    # models_points = get_dd_models_points(
    #     qfrdl_bdds_points, qfrdl_ldds_points)
    # build_time_graph(time_points, "T-OBDD", "LDD",
    #                  "plots/smtlib/QF_RDL/ldd_vs_tbdd_time.pdf")
    # build_size_graph(size_points, "T-OBDD", "LDD",
    #                  "plots/smtlib/QF_RDL/ldd_vs_tbdd_size.pdf")
    # build_models_graph(models_points, "T-OBDD", "LDD",
    #                    "plots/smtlib/QF_RDL/ldd_vs_tbdd_models.pdf")

    print("QF RDL Opt vs No Opt graphs")
    time_points = get_time_points(
        qfrdl_bdds_points, qfrdl_bdds_noeqsplit_points)
    size_points = get_nodes_points(
        qfrdl_bdds_points, qfrdl_bdds_noeqsplit_points)
    models_points = get_dd_models_points(
        qfrdl_bdds_points, qfrdl_bdds_noeqsplit_points)
    lemmas_points = get_lemmas_points(
        qfrdl_bdds_points, qfrdl_bdds_noeqsplit_points)
    fresh_atoms_points = get_dd_fresh_atoms_points(
        qfrdl_bdds_points, qfrdl_bdds_noeqsplit_points)
    build_time_graph(time_points, "No Opt", "Opt")
    build_size_graph(size_points, "No Opt", "Opt")
    build_models_graph(models_points, "No Opt", "Opt")
    build_lemmas_graph(lemmas_points, "No Opt", "Opt")
    print(fresh_atoms_points)
    build_models_graph(fresh_atoms_points, "No Opt", "Opt")

    # lemmas_points = get_lemmas_points(
    #     qfrdl_tmp, qfrdl_tmp_noeqsplit)
    # print(len(qfrdl_tmp))
    # print(len(qfrdl_tmp_noeqsplit))
    # build_lemmas_graph(lemmas_points, "No Opt", "Opt")

    # print("QF RDL BDD graphs")
    # time_points = get_time_points(
    #     qfrdl_bdds_points, qfrdl_abstraction_bdd_points)
    # size_points = get_nodes_points(
    #     qfrdl_bdds_points, qfrdl_abstraction_bdd_points)
    # models_points = get_dd_models_points(
    #     qfrdl_bdds_points, qfrdl_abstraction_bdd_points)
    # build_time_graph(time_points, "T-OBDD", "Abs. BDD",
    #                  "plots/smtlib/QF_RDL/abstr_bdd_vs_tbdd_time.pdf")
    # build_size_graph(size_points, "T-OBDD", "Abs. BDD",
    #                  "plots/smtlib/QF_RDL/abstr_bdd_vs_tbdd_size.pdf")
    # build_models_graph(models_points, "T-OBDD", "Abs. BDD",
    #                    "plots/smtlib/QF_RDL/abstr_bdd_vs_tbdd_models.pdf")

    # print("QF RDL SDD graphs")
    # time_points = get_time_points(
    #     qfrdl_sdds_points, qfrdl_abstraction_sdd_points)
    # size_points = get_nodes_points(
    #     qfrdl_sdds_points, qfrdl_abstraction_sdd_points)
    # build_time_graph(time_points, "T-SDD", "Abs. SDD",
    #                  "plots/smtlib/QF_RDL/abstr_sdd_vs_tsdd_time.pdf")
    # build_size_graph(size_points, "T-SDD", "Abs. SDD",
    #                  "plots/smtlib/QF_RDL/abstr_sdd_vs_tsdd_size.pdf")

    # --------------------------------------------------------------
    # SMTLIB QF UF

    # DATA NOT READY: parsing/msat problem

    # qfuf_bdds_points = get_smtlib_bench_data(
    #     "T-BDD", "benchmarks/smtlib/output_bdd/non-incremental/QF_UF")
    # qfuf_abstraction_bdd_points = get_smtlib_bench_data(
    #     "Abstraction BDD", "benchmarks/smtlib/output_abstraction_bdd/non-incremental/QF_UF")
    # qfuf_sdds_points = get_smtlib_bench_data(
    #     "T-SDD", "benchmarks/smtlib/output_sdd/non-incremental/QF_UF")
    # qfuf_abstraction_sdd_points = get_smtlib_bench_data(
    #     "Abstraction SDD", "benchmarks/smtlib/output_abstraction_sdd/non-incremental/QF_UF")

    # time_points = get_time_points(
    #     qfuf_bdds_points, qfuf_abstraction_bdd_points)
    # size_points = get_nodes_points(
    #     qfuf_bdds_points, qfuf_abstraction_bdd_points)
    # models_points = get_dd_models_points(
    #     qfuf_bdds_points, qfuf_abstraction_bdd_points)
    # build_time_graph(time_points, "T-BDD", "Abs. BDD",
    #                  "plots/smtlib/QF_UF/abstr_bdd_vs_tbdd_time.pdf")
    # build_size_graph(size_points, "T-BDD", "Abs. BDD",
    #                  "plots/smtlib/QF_UF/abstr_bdd_vs_tbdd_size.pdf")
    # build_models_graph(models_points, "T-BDD", "Abs. BDD",
    #                  "plots/smtlib/QF_UF/abstr_bdd_vs_tbdd_models.pdf")
    # time_points = get_time_points(
    #     qfuf_sdds_points, qfuf_abstraction_sdd_points)
    # size_points = get_nodes_points(
    #     qfuf_sdds_points, qfuf_abstraction_sdd_points)
    # build_time_graph(time_points, "T-SDD", "Abs. SDD",
    #                  "plots/smtlib/QF_UF/abstr_sdd_vs_tsdd_time.pdf")
    # build_size_graph(size_points, "T-SDD", "Abs. SDD",
    #                  "plots/smtlib/QF_UF/abstr_sdd_vs_tsdd_size.pdf")

    # --------------------------------------------------------------
    # SMTLIB QF UFLRA

    # DATA NOT READY: parsing/msat problem

    # qfuflra_ldds_points = get_smtlib_bench_data(
    #     "LDD", "benchmarks/smtlib/output_ldd/non-incremental/QF_UFLRA")
    # qfuflra_bdds_points = get_smtlib_bench_data(
    #     "T-BDD", "benchmarks/smtlib/output_bdd/non-incremental/QF_UFLRA")
    # qfuflra_abstraction_bdd_points = get_smtlib_bench_data(
    #     "Abstraction BDD", "benchmarks/smtlib/output_abstraction_bdd/non-incremental/QF_UFLRA")
    # qfuflra_sdds_points = get_smtlib_bench_data(
    #     "T-SDD", "benchmarks/smtlib/output_sdd/non-incremental/QF_RDL")
    # qfuflra_abstraction_sdd_points = get_smtlib_bench_data(
    #     "Abstraction SDD", "benchmarks/smtlib/output_abstraction_sdd/non-incremental/QF_UFLRA")

    # time_points = get_time_points(
    #     qfuflra_bdds_points, qfuflra_ldds_points)
    # size_points = get_nodes_points(
    #     qfuflra_bdds_points, qfuflra_ldds_points)
    # models_points = get_dd_models_points(
    #     qfuflra_bdds_points, qfuflra_ldds_points)
    # build_time_graph(time_points, "T-BDD", "LDD",
    #                  "plots/smtlib/UFLRA/ldd_vs_tbdd_time.pdf")
    # build_size_graph(size_points, "T-BDD", "LDD",
    #                  "plots/smtlib/UFLRA/ldd_vs_tbdd_size.pdf")
    # build_models_graph(models_points, "T-BDD", "LDD",
    #                  "plots/smtlib/UFLRA/ldd_vs_tbdd_models.pdf")
    # time_points = get_time_points(
    #     qfuflra_bdds_points, qfuflra_abstraction_bdd_points)
    # size_points = get_nodes_points(
    #     qfuflra_bdds_points, qfuflra_abstraction_bdd_points)
    # models_points = get_dd_models_points(
    #     qfuflra_bdds_points, qfuflra_abstraction_bdd_points)
    # build_time_graph(time_points, "T-BDD", "Abs. BDD",
    #                  "plots/smtlib/UFLRA/abstr_bdd_vs_tbdd_time.pdf")
    # build_size_graph(size_points, "T-BDD", "Abs. BDD",
    #                  "plots/smtlib/UFLRA/abstr_bdd_vs_tbdd_size.pdf")
    # build_models_graph(models_points, "T-BDD", "Abs. BDD",
    #                  "plots/smtlib/UFLRA/abstr_bdd_vs_tbdd_models.pdf")
    # time_points = get_time_points(
    #     qfuflra_sdds_points, qfuflra_abstraction_sdd_points)
    # size_points = get_nodes_points(
    #     qfuflra_sdds_points, qfuflra_abstraction_sdd_points)
    # build_time_graph(time_points, "T-SDD", "Abs. SDD",
    #                  "plots/smtlib/UFLRA/abstr_sdd_vs_tsdd_time.pdf")
    # build_size_graph(size_points, "T-SDD", "Abs. SDD",
    #                  "plots/smtlib/UFLRA/abstr_sdd_vs_tsdd_size.pdf")


def test_plotting_lib() -> None:
    """test plotting lib"""
    x = [5, 7, 8, 7, 2, 17, 2, 9, 4, 11, 12, 9, 6]
    y = [99, 86, 87, 88, 111, 86, 103, 87, 94, 78, 77, 85, 86]
    plt.scatter(x, y)
    plt.show()


if __name__ == "__main__":
    main()
