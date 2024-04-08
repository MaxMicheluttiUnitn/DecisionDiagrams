"""main and functions to plot the results of the program running on benchmarks"""
from enum import Enum
import json
import os
from dataclasses import dataclass
# from pprint import pprint
from typing import List, Tuple
import matplotlib.pyplot as plt


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
            points.append(Point(DataSource.THEORY_SDD,
                          0, 0, 0, 0, 0, "mutex/"+filename, True))
            continue
        if data.get("All-SAT computation time") is not None:
            allsmttime = data.get("All-SAT computation time")
        else:
            allsmttime = 1000
        points.append(Point(DataSource.THEORY_SDD,
                            data["total computation time"],
                            allsmttime,
                            data[kind]["total processing time"],
                            data[kind]["model count"],
                            data[kind]["DD nodes"], "mutex/"+filename, False))

    # retrieving xor result
    files = os.listdir(source+"/xor")
    for filename in files:
        f = open(source+"/xor/"+filename, encoding="utf8")
        data = json.load(f)
        if len(data) == 0 or data.get("timeout") is not None:
            points.append(Point(DataSource.THEORY_SDD,
                          0, 0, 0, 0, 0, "xor/"+filename, True))
            continue
        if data.get("All-SAT computation time") is not None:
            allsmttime = data.get("All-SAT computation time")
        else:
            allsmttime = 1000
        points.append(Point(DataSource.THEORY_SDD,
                            data["total computation time"],
                            allsmttime,
                            data[kind]["total processing time"],
                            data[kind]["model count"],
                            data[kind]["DD nodes"], "xor/"+filename,
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
            points.append(Point(DataSource.THEORY_BDD, 0, 0, 0, 0, 0, filename.replace(
                source+"/", ''), True))
            continue
        if data.get("All-SMT computation time") is not None:
            allsmttime = data["All-SMT computation time"]
        else:
            allsmttime = 0.1
        points.append(Point(DataSource.THEORY_BDD,
                            data["total computation time"],
                            allsmttime,
                            data[kind]["total DD computation time"],
                            data[kind]["DD models"],
                            data[kind]["DD nodes"],
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
            points.append(Point(DataSource.THEORY_BDD, 0, 0, 0, 0, 0, filename.replace(
                source+"/", ''), True))
            continue
        if data.get("All-SMT computation time") is not None:
            allsmttime = data["All-SMT computation time"]
        else:
            allsmttime = 0.1

        points.append(Point(DataSource.THEORY_BDD,
                            data["total computation time"],
                            allsmttime,
                            data[kind]["total DD computation time"],
                            data[kind]["DD models"],
                            data[kind]["DD nodes"],
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
        f = open(filename, encoding="utf8")
        data = json.load(f)
        if len(data) == 0 or data.get("timeout") is not None:
            points.append(Point(DataSource.THEORY_BDD, 0, 0, 0, 0, 0, filename.replace(
                source+"/", ''), True))
            continue
        if data.get("All-SMT computation time") is not None:
            allsmttime = data["All-SMT computation time"]
        else:
            allsmttime = 3600

        if data.get(kind).get("total DD computation time") is not None:
            ddtime = data[kind]["total DD computation time"]
        elif data.get(kind).get("total processing time") is not None:
            ddtime = data[kind]["total processing time"]
        else:
            ddtime = 3600

        if data.get(kind).get("DD models") is not None:
            ddmodels = data[kind]["DD models"]
        else:
            ddmodels = None

        points.append(Point(DataSource.THEORY_BDD,
                            data["total computation time"],
                            allsmttime,
                            ddtime,
                            ddmodels,
                            data[kind]["DD nodes"],
                            filename.replace(source+"/", ''), False))
    return points


def get_time_points(
        theory_points: List[Point],
        abstraction_points: List[Point]) -> Tuple[List[float], List[float], int]:
    """translate data into plottable points comparing time"""
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


def get_nodes_points(
        theory_points: List[Point],
        abstraction_points: List[Point]) -> Tuple[List[float], List[float], int]:
    """translate data into plottable points comparing DD size in nodes"""
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

    edge = max(max_theory, max_abstraction) * 10

    for t_p in theory_points:
        if t_p.timeout:
            t_p.dd_nodes = edge
    for a_p in abstraction_points:
        if a_p.timeout:
            a_p.dd_nodes = edge

    # count11 = 0
    for t_p in theory_points:
        for a_p in abstraction_points:
            if t_p.title == a_p.title:
                # if t_p.dd_nodes == 1 and a_p.dd_nodes == 1:
                #     count11 += 1
                theory_list.append(t_p.dd_nodes)
                abstraction_list.append(a_p.dd_nodes)
                break
    # print("Count 1 1", count11)
    return (theory_list, abstraction_list, edge)


def get_dd_models_points(
        theory_points: List[Point],
        abstraction_points: List[Point]) -> Tuple[List[float], List[float], int]:
    """translate data into plottable points comparing DD size in nodes"""
    theory_list = []
    abstraction_list = []
    max_theory = theory_points[0].dd_models
    max_abstraction = abstraction_points[0].dd_models

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
            if t_p.title == a_p.title and t_p.dd_models is not None and a_p.dd_models is not None:
                # if t_p.dd_nodes == 1 and a_p.dd_nodes == 1:
                #     count11 += 1
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

    plt.scatter(time_points[0], time_points[1], marker='s')
    plt.xlabel(x_label)
    plt.ylabel(y_label)
    plt.title("Computation Time")
    ax = plt.gca()
    ax.set_yscale('log')
    ax.set_xscale('log')
    ax.set_aspect('equal', adjustable='box')
    diag_line, = ax.plot(ax.get_xlim(), ax.get_ylim(), ls="--", c=".3")

    def on_change_time(_axes):
        x_lims = ax.get_xlim()
        y_lims = ax.get_ylim()
        diag_line.set_data(x_lims, y_lims)
    ax.callbacks.connect('xlim_changed', on_change_time)
    ax.callbacks.connect('ylim_changed', on_change_time)
    plt.axvline(x=time_points[2], ls="--", c=".3")
    plt.axhline(y=time_points[2], ls="--", c=".3")
    plt.xlim((0.0001, 1000000))
    plt.ylim((0.0001, 1000000))
    # plt.axis('square')

    if file is not None:
        plt.savefig(file, bbox_inches='tight')
    plt.show()


def build_size_graph(size_points, x_label: str, y_label: str, file: str | None = None) -> None:
    """builds and shows the size graph"""
    plt.scatter(size_points[0], size_points[1], marker='s')
    plt.xlabel(x_label)
    plt.ylabel(y_label)
    plt.title("DD size in nodes")
    ax = plt.gca()
    ax.set_yscale('log')
    ax.set_xscale('log')
    ax.set_aspect('equal', adjustable='box')
    diag_line, = ax.plot(ax.get_xlim(), ax.get_ylim(), ls="--", c=".3")

    def on_change(_axes):
        x_lims = ax.get_xlim()
        y_lims = ax.get_ylim()
        diag_line.set_data(x_lims, y_lims)
    ax.callbacks.connect('xlim_changed', on_change)
    ax.callbacks.connect('ylim_changed', on_change)
    # plt.axis('square')
    plt.axvline(x=size_points[2], ls="--", c=".3")
    plt.axhline(y=size_points[2], ls="--", c=".3")
    plt.xlim((1, 100000))
    plt.ylim((1, 100000))

    if file is not None:
        plt.savefig(file, bbox_inches='tight')
    plt.show()


def build_models_graph(points, x_label: str, y_label: str, file: str | None = None) -> None:
    """builds and shows the model count graph"""
    plt.scatter(points[0], points[1], marker='s')
    plt.xlabel(x_label)
    plt.ylabel(y_label)
    plt.title("DD amount of models")
    ax = plt.gca()
    ax.set_yscale('log')
    ax.set_xscale('log')
    ax.set_aspect('equal', adjustable='box')
    diag_line, = ax.plot(ax.get_xlim(), ax.get_ylim(), ls="--", c=".3")

    def on_change(_axes):
        x_lims = ax.get_xlim()
        y_lims = ax.get_ylim()
        diag_line.set_data(x_lims, y_lims)
    ax.callbacks.connect('xlim_changed', on_change)
    ax.callbacks.connect('ylim_changed', on_change)
    # plt.axis('square')
    plt.axvline(x=points[2], ls="--", c=".3")
    plt.axhline(y=points[2], ls="--", c=".3")
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

    # time_points = get_time_points(
    #     wmi_bdds_points, wmi_abstraction_bdd_points)
    # size_points = get_nodes_points(
    #     wmi_bdds_points, wmi_abstraction_bdd_points)
    # models_points = get_dd_models_points(
    #     wmi_bdds_points, wmi_abstraction_bdd_points)
    # build_time_graph(time_points, "T-BDD", "Abs. BDD",
    #                  "plots/wmi/abstr_bdd_vs_tbdd_time.png")
    # build_size_graph(size_points, "T-BDD", "Abs. BDD",
    #                  "plots/wmi/abstr_bdd_vs_tbdd_size.png")
    # build_models_graph(size_points, "T-BDD", "Abs. BDD",
    #                    "plots/wmi/abstr_bdd_vs_tbdd_models.png")

    # time_points = get_time_points(
    #     wmi_sdds_points, wmi_abstraction_sdd_points)
    # size_points = get_nodes_points(
    #     wmi_sdds_points, wmi_abstraction_sdd_points)
    # build_time_graph(time_points, "T-SDD", "Abs. SDD",
    #                  "plots/wmi/abstr_sdd_vs_tsdd_time.png")
    # build_size_graph(size_points, "T-SDD", "Abs. SDD",
    #                  "plots/wmi/abstr_sdd_vs_tsdd_size.png")

    # --------------------------------------------------------------
    # LDD RANDGEN

    ldd_randgen_ldds_points = get_ldd_randgen_bench_data(
        "LDD", "benchmarks/ldd_randgen/output_ldd")
    ldd_randgen_bdds_points = get_ldd_randgen_bench_data(
        "T-BDD", "benchmarks/ldd_randgen/output")
    ldd_randgen_abstraction_bdd_points = get_ldd_randgen_bench_data(
        "Abstraction BDD", "benchmarks/ldd_randgen/output_abstraction")
    ldd_randgen_sdds_points = get_ldd_randgen_bench_data(
        "T-SDD", "benchmarks/ldd_randgen/output_sdd")
    ldd_randgen_abstraction_sdd_points = get_ldd_randgen_bench_data(
        "Abstraction SDD", "benchmarks/ldd_randgen/output_abstraction_sdd")
    ldd_randgen_bdds_newgen_points = get_ldd_randgen_bench_data(
        "T-BDD", "benchmarks/ldd_randgen/output_newddgen")

    time_points = get_time_points(
        ldd_randgen_bdds_points, ldd_randgen_ldds_points)
    size_points = get_nodes_points(
        ldd_randgen_bdds_points, ldd_randgen_ldds_points)
    models_points = get_dd_models_points(
        ldd_randgen_bdds_points, ldd_randgen_ldds_points)
    build_time_graph(time_points, "T-BDD", "LDD",
                     "plots/ldd_randgen/ldd_vs_tbdd_time.png")
    build_size_graph(size_points, "T-BDD", "LDD",
                     "plots/ldd_randgen/ldd_vs_tbdd_size.png")
    build_models_graph(size_points, "T-BDD", "LDD",
                       "plots/ldd_randgen/ldd_vs_tbdd_models.png")

    time_points = get_time_points(
        ldd_randgen_bdds_points, ldd_randgen_abstraction_bdd_points)
    size_points = get_nodes_points(
        ldd_randgen_bdds_points, ldd_randgen_abstraction_bdd_points)
    models_points = get_dd_models_points(
        ldd_randgen_bdds_points, ldd_randgen_abstraction_bdd_points)
    build_time_graph(time_points, "T-BDD", "Abs. BDD",
                     "plots/ldd_randgen/abstr_bdd_vs_tbdd_time.png")
    build_size_graph(size_points, "T-BDD", "Abs. BDD",
                     "plots/ldd_randgen/abstr_bdd_vs_tbdd_size.png")
    build_models_graph(size_points, "T-BDD", "Abs. BDD",
                       "plots/ldd_randgen/abstr_bdd_vs_tbdd_models.png")

    time_points = get_time_points(
        ldd_randgen_sdds_points, ldd_randgen_abstraction_sdd_points)
    size_points = get_nodes_points(
        ldd_randgen_sdds_points, ldd_randgen_abstraction_sdd_points)
    build_time_graph(time_points, "T-SDD", "Abs. SDD",
                     "plots/ldd_randgen/abstr_sdd_vs_tsdd_time.png")
    build_size_graph(size_points, "T-SDD", "Abs. SDD",
                     "plots/ldd_randgen/abstr_sdd_vs_tsdd_size.png")

    time_points = get_dd_time_points(
        ldd_randgen_bdds_points, ldd_randgen_bdds_newgen_points)
    size_points = get_nodes_points(
        ldd_randgen_bdds_points, ldd_randgen_bdds_newgen_points)
    models_points = get_dd_models_points(
        ldd_randgen_bdds_points, ldd_randgen_bdds_newgen_points)
    build_time_graph(time_points, "Old DD", "New DD",
                     "plots/ldd_randgen/old_vs_new_dd_time.png")
    build_size_graph(size_points, "Old DD", "New DD",
                     "plots/ldd_randgen/old_vs_new_dd_size.png")
    build_models_graph(models_points, "Old DD", "New DD",
                       "plots/ldd_randgen/old_vs_new_dd_models.png")

    # --------------------------------------------------------------
    # RANDGEN

    # randgen_bdds_points = get_randgen_bench_data(
    #     "T-BDD", "benchmarks/randgen/output_tsetsin")
    # randgen_abstraction_bdd_points = get_randgen_bench_data(
    #     "Abstraction BDD", "benchmarks/randgen/output_abstraction")
    # randgen_sdds_points = get_randgen_bench_data(
    #     "T-SDD", "benchmarks/randgen/output_sdd")
    # randgen_abstraction_sdd_points = get_randgen_bench_data(
    #     "Abstraction SDD", "benchmarks/randgen/output_abstraction_sdd")

    # time_points = get_time_points(
    #     randgen_bdds_points, randgen_abstraction_bdd_points)
    # size_points = get_nodes_points(
    #     randgen_bdds_points, randgen_abstraction_bdd_points)
    # build_time_graph(time_points, "T-BDD", "Abs. BDD",
    #                  "plots/randgen/abstr_bdd_vs_tbdd_time.png")
    # build_size_graph(size_points, "T-BDD", "Abs. BDD",
    #                  "plots/randgen/abstr_bdd_vs_tbdd_size.png")
    # time_points = get_time_points(
    #     randgen_sdds_points, randgen_abstraction_sdd_points)
    # size_points = get_nodes_points(
    #     randgen_sdds_points, randgen_abstraction_sdd_points)
    # build_time_graph(time_points, "T-SDD", "Abs. SDD",
    #                  "plots/randgen/abstr_sdd_vs_tsdd_time.png")
    # build_size_graph(size_points, "T-SDD", "Abs. SDD",
    #                  "plots/randgen/abstr_sdd_vs_tsdd_size.png")

    # --------------------------------------------------------------
    # SMTLIB QF RDL

    # qfrdl_ldds_points = get_smtlib_bench_data(
    #     "LDD", "benchmarks/smtlib/output_ldd/non-incremental/QF_RDL")
    # qfrdl_bdds_points = get_smtlib_bench_data(
    #     "T-BDD", "benchmarks/smtlib/output_bdd/non-incremental/QF_RDL")
    # qfrdl_abstraction_bdd_points = get_smtlib_bench_data(
    #     "Abstraction BDD", "benchmarks/smtlib/output_abstraction_bdd/non-incremental/QF_RDL")
    # qfrdl_sdds_points = get_smtlib_bench_data(
    #     "T-SDD", "benchmarks/smtlib/output_sdd/non-incremental/QF_RDL")
    # qfrdl_abstraction_sdd_points = get_smtlib_bench_data(
    #     "Abstraction SDD", "benchmarks/smtlib/output_abstraction_sdd/non-incremental/QF_RDL")

    # time_points = get_time_points(
    #     qfrdl_bdds_points, qfrdl_ldds_points)
    # size_points = get_nodes_points(
    #     qfrdl_bdds_points, qfrdl_ldds_points)
    # models_points = get_dd_models_points(
    #     qfrdl_bdds_points, qfrdl_ldds_points)
    # build_time_graph(time_points, "T-BDD", "LDD",
    #                  "plots/smtlib/QF_RDL/ldd_vs_tbdd_time.png")
    # build_size_graph(size_points, "T-BDD", "LDD",
    #                  "plots/smtlib/QF_RDL/ldd_vs_tbdd_size.png")
    # build_models_graph(size_points, "T-BDD", "LDD",
    #                    "plots/smtlib/QF_RDL/ldd_vs_tbdd_models.png")
    # time_points = get_time_points(
    #     qfrdl_bdds_points, qfrdl_abstraction_bdd_points)
    # size_points = get_nodes_points(
    #     qfrdl_bdds_points, qfrdl_abstraction_bdd_points)
    # build_time_graph(time_points, "T-BDD", "Abs. BDD",
    #                  "plots/smtlib/QF_RDL/abstr_bdd_vs_tbdd_time.png")
    # build_size_graph(size_points, "T-BDD", "Abs. BDD",
    #                  "plots/smtlib/QF_RDL/abstr_bdd_vs_tbdd_size.png")
    # time_points = get_time_points(
    #     qfrdl_sdds_points, qfrdl_abstraction_sdd_points)
    # size_points = get_nodes_points(
    #     qfrdl_sdds_points, qfrdl_abstraction_sdd_points)
    # build_time_graph(time_points, "T-SDD", "Abs. SDD",
    #                  "plots/smtlib/QF_RDL/abstr_sdd_vs_tsdd_time.png")
    # build_size_graph(size_points, "T-SDD", "Abs. SDD",
    #                  "plots/smtlib/QF_RDL/abstr_sdd_vs_tsdd_size.png")

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
    #                  "plots/smtlib/QF_UF/abstr_bdd_vs_tbdd_time.png")
    # build_size_graph(size_points, "T-BDD", "Abs. BDD",
    #                  "plots/smtlib/QF_UF/abstr_bdd_vs_tbdd_size.png")
    # build_models_graph(models_points, "T-BDD", "Abs. BDD",
    #                  "plots/smtlib/QF_UF/abstr_bdd_vs_tbdd_models.png")
    # time_points = get_time_points(
    #     qfuf_sdds_points, qfuf_abstraction_sdd_points)
    # size_points = get_nodes_points(
    #     qfuf_sdds_points, qfuf_abstraction_sdd_points)
    # build_time_graph(time_points, "T-SDD", "Abs. SDD",
    #                  "plots/smtlib/QF_UF/abstr_sdd_vs_tsdd_time.png")
    # build_size_graph(size_points, "T-SDD", "Abs. SDD",
    #                  "plots/smtlib/QF_UF/abstr_sdd_vs_tsdd_size.png")

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
    #                  "plots/smtlib/UFLRA/ldd_vs_tbdd_time.png")
    # build_size_graph(size_points, "T-BDD", "LDD",
    #                  "plots/smtlib/UFLRA/ldd_vs_tbdd_size.png")
    # build_models_graph(models_points, "T-BDD", "LDD",
    #                  "plots/smtlib/UFLRA/ldd_vs_tbdd_models.png")
    # time_points = get_time_points(
    #     qfuflra_bdds_points, qfuflra_abstraction_bdd_points)
    # size_points = get_nodes_points(
    #     qfuflra_bdds_points, qfuflra_abstraction_bdd_points)
    # models_points = get_dd_models_points(
    #     qfuflra_bdds_points, qfuflra_abstraction_bdd_points)
    # build_time_graph(time_points, "T-BDD", "Abs. BDD",
    #                  "plots/smtlib/UFLRA/abstr_bdd_vs_tbdd_time.png")
    # build_size_graph(size_points, "T-BDD", "Abs. BDD",
    #                  "plots/smtlib/UFLRA/abstr_bdd_vs_tbdd_size.png")
    # build_models_graph(models_points, "T-BDD", "Abs. BDD",
    #                  "plots/smtlib/UFLRA/abstr_bdd_vs_tbdd_models.png")
    # time_points = get_time_points(
    #     qfuflra_sdds_points, qfuflra_abstraction_sdd_points)
    # size_points = get_nodes_points(
    #     qfuflra_sdds_points, qfuflra_abstraction_sdd_points)
    # build_time_graph(time_points, "T-SDD", "Abs. SDD",
    #                  "plots/smtlib/UFLRA/abstr_sdd_vs_tsdd_time.png")
    # build_size_graph(size_points, "T-SDD", "Abs. SDD",
    #                  "plots/smtlib/UFLRA/abstr_sdd_vs_tsdd_size.png")


def test_plotting_lib() -> None:
    """test plotting lib"""
    x = [5, 7, 8, 7, 2, 17, 2, 9, 4, 11, 12, 9, 6]
    y = [99, 86, 87, 88, 111, 86, 103, 87, 94, 78, 77, 85, 86]
    plt.scatter(x, y)
    plt.show()


if __name__ == "__main__":
    main()
