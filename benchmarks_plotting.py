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
    allSMT_time: float
    dd_nodes: int
    title: str
    timeout: bool


def get_abstraction_sdd_from_wmi_bench_data() -> List[Point]:
    """gets the computation data from a run generating T-SDDs from the WMI benchmark problems"""
    points = []

    # retrieving mutex result
    files = os.listdir("benchmarks/wmi/output_abstraction_sdd/mutex")
    files.sort()
    for filename in files:
        f = open("benchmarks/wmi/output_abstraction_sdd/mutex/" +
                 filename, encoding="utf8")
        data = json.load(f)
        if len(data) == 0 or data.get("timeout") is not None:
            points.append(Point(DataSource.ABSTRACTION_BDD,
                          0, 0, 0, "mutex/"+filename, True))
            continue
        points.append(Point(DataSource.ABSTRACTION_BDD,
                            data["total computation time"],
                            data["All-SMT computation time"],
                            data["T-SDD"]["DD nodes"],
                            "mutex/"+filename,
                            False))

    # retrieving xor result
    files = os.listdir("benchmarks/wmi/output_abstraction_sdd/xor")
    files.sort()
    for filename in files:
        f = open("benchmarks/wmi/output_abstraction_sdd/xor/" +
                 filename, encoding="utf8")
        data = json.load(f)
        if len(data) == 0 or data.get("timeout") is not None:
            points.append(Point(DataSource.ABSTRACTION_BDD,
                          0, 0, 0, "xor/"+filename, True))
            continue
        points.append(Point(DataSource.ABSTRACTION_BDD,
                            data["total computation time"],
                            data["All-SMT computation time"],
                            data["T-SDD"]["DD nodes"],
                            "xor/"+filename,
                            False))

    return points


def get_abstraction_bdd_from_wmi_bench_data() -> List[Point]:
    """gets the computation data from a run generating T-BDDs from the WMI benchmark problems"""
    points = []

    # retrieving mutex result
    files = os.listdir("benchmarks/wmi/output_abstraction/mutex")
    files.sort()
    for filename in files:
        f = open("benchmarks/wmi/output_abstraction/mutex/" +
                 filename, encoding="utf8")
        data = json.load(f)
        if len(data) == 0 or data.get("timeout") is not None:
            points.append(Point(DataSource.ABSTRACTION_BDD,
                          0, 0, 0, "mutex/"+filename, True))
            continue
        points.append(Point(DataSource.ABSTRACTION_BDD,
                            data["total computation time"],
                            data["All-SMT computation time"],
                            data["T-BDD"]["DD nodes"], "mutex/"+filename, False))

    # retrieving xor result
    files = os.listdir("benchmarks/wmi/output_abstraction/xor")
    files.sort()
    for filename in files:
        f = open("benchmarks/wmi/output_abstraction/xor/" +
                 filename, encoding="utf8")
        data = json.load(f)
        if len(data) == 0 or data.get("timeout") is not None:
            points.append(Point(DataSource.ABSTRACTION_BDD,
                          0, 0, 0, "xor/"+filename, True))
            continue
        points.append(Point(DataSource.ABSTRACTION_BDD,
                            data["total computation time"],
                            data["All-SMT computation time"],
                            data["T-BDD"]["DD nodes"],
                            "xor/"+filename,
                            False))

    return points


def get_theory_sdd_from_wmi_bench_data() -> List[Point]:
    """gets the computation data from a run generating T-SDDs from the WMI benchmark problems"""
    points = []

    # retrieving mutex result
    files = os.listdir("benchmarks/wmi/output_sdd/mutex")
    for filename in files:
        f = open("benchmarks/wmi/output_sdd/mutex/"+filename, encoding="utf8")
        data = json.load(f)
        if len(data) == 0 or data.get("timeout") is not None:
            points.append(Point(DataSource.THEORY_SDD,
                          0, 0, 0, "mutex/"+filename, True))
            continue
        points.append(Point(DataSource.THEORY_SDD,
                            data["total computation time"],
                            data["All-SMT computation time"],
                            data["T-SDD"]["DD nodes"], "mutex/"+filename, False))

    # retrieving xor result
    files = os.listdir("benchmarks/wmi/output_sdd/xor")
    for filename in files:
        f = open("benchmarks/wmi/output_sdd/xor/"+filename, encoding="utf8")
        data = json.load(f)
        if len(data) == 0 or data.get("timeout") is not None:
            points.append(Point(DataSource.THEORY_SDD,
                          0, 0, 0, "xor/"+filename, True))
            continue
        points.append(Point(DataSource.THEORY_SDD,
                            data["total computation time"],
                            data["All-SMT computation time"],
                            data["T-SDD"]["DD nodes"], "xor/"+filename,
                            False))

    return points


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
                          0, 0, 0, "mutex/"+filename, True))
            continue
        points.append(Point(DataSource.THEORY_SDD,
                            data["total computation time"],
                            data["All-SMT computation time"],
                            data[kind]["DD nodes"], "mutex/"+filename, False))

    # retrieving xor result
    files = os.listdir(source+"/xor")
    for filename in files:
        f = open(source+"/xor/"+filename, encoding="utf8")
        data = json.load(f)
        if len(data) == 0 or data.get("timeout") is not None:
            points.append(Point(DataSource.THEORY_SDD,
                          0, 0, 0, "xor/"+filename, True))
            continue
        points.append(Point(DataSource.THEORY_SDD,
                            data["total computation time"],
                            data["All-SMT computation time"],
                            data[kind]["DD nodes"], "xor/"+filename,
                            False))

    return points


def get_theory_bdd_from_wmi_bench_data() -> List[Point]:
    """gets the computation data from a run generating T-BDDs from the WMI benchmark problems"""
    points = []

    # retrieving mutex result
    files = os.listdir("benchmarks/wmi/output/mutex")
    for filename in files:
        f = open("benchmarks/wmi/output/mutex/"+filename, encoding="utf8")
        data = json.load(f)
        if len(data) == 0 or data.get("timeout") is not None:
            points.append(Point(DataSource.THEORY_BDD,
                          0, 0, 0, "mutex/"+filename, True))
            continue
        points.append(Point(DataSource.THEORY_BDD,
                            data["total computation time"],
                            data["All-SMT computation time"],
                            data["T-BDD"]["DD nodes"], "mutex/"+filename, False))

    # retrieving xor result
    files = os.listdir("benchmarks/wmi/output/xor")
    for filename in files:
        f = open("benchmarks/wmi/output/xor/"+filename, encoding="utf8")
        data = json.load(f)
        if len(data) == 0 or data.get("timeout") is not None:
            points.append(Point(DataSource.THEORY_BDD,
                          0, 0, 0, "xor/"+filename, True))
            continue
        points.append(Point(DataSource.THEORY_BDD,
                            data["total computation time"],
                            data["All-SMT computation time"],
                            data["T-BDD"]["DD nodes"], "xor/"+filename,
                            False))

    return points


def get_theory_bdd_from_randgen_bench_data() -> List[Point]:
    """gets the computation data from a run generating T-BDDs 
    from the randomly generated benchmark problems"""
    points = []
    files_list: List[str] = []
    for path, _subdirs, files in os.walk("benchmarks/randgen/output"):
        for name in files:
            files_list.append(os.path.join(path, name))
    for filename in files_list:
        f = open(filename, encoding="utf8")
        data = json.load(f)
        if len(data) == 0 or data.get("timeout") is not None:
            points.append(Point(DataSource.THEORY_BDD, 0, 0, 0, filename.replace(
                'benchmarks/randgen/output/', ''), True))
            continue
        points.append(Point(DataSource.THEORY_BDD,
                            data["total computation time"],
                            data["All-SMT computation time"],
                            data["T-BDD"]["DD nodes"],
                            filename.replace('benchmarks/randgen/output/', ''), False))
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
            points.append(Point(DataSource.THEORY_BDD, 0, 0, 0, filename.replace(
                source+"/", ''), True))
            continue
        if data.get("All-SMT computation time") is not None:
            allsmttime = data["All-SMT computation time"]
        else:
            allsmttime = 0.1

        points.append(Point(DataSource.THEORY_BDD,
                            data["total computation time"],
                            allsmttime,
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
            points.append(Point(DataSource.THEORY_BDD, 0, 0, 0, filename.replace(
                source+"/", ''), True))
            continue
        if data.get("All-SMT computation time") is not None:
            allsmttime = data["All-SMT computation time"]
        else:
            allsmttime = 0.1

        points.append(Point(DataSource.THEORY_BDD,
                            data["total computation time"],
                            allsmttime,
                            data[kind]["DD nodes"],
                            filename.replace(source+"/", ''), False))
    return points


def get_smtlib_QF_RDL_bench_data(kind: str, source: str) -> List[Point]:
    """gets the computation data from a run on smtlib QF RDL benchmark problems"""
    points = []
    files_list: List[str] = []
    for path, _subdirs, files in os.walk(source):
        for name in files:
            files_list.append(os.path.join(path, name))
    for filename in files_list:
        f = open(filename, encoding="utf8")
        data = json.load(f)
        if len(data) == 0 or data.get("timeout") is not None:
            points.append(Point(DataSource.THEORY_BDD, 0, 0, 0, filename.replace(
                source+"/", ''), True))
            continue
        if data.get("All-SMT computation time") is not None:
            allsmttime = data["All-SMT computation time"]
        else:
            allsmttime = 1000

        points.append(Point(DataSource.THEORY_BDD,
                            data["total computation time"],
                            allsmttime,
                            data[kind]["DD nodes"],
                            filename.replace(source+"/", ''), False))
    return points


def get_theory_sdd_from_randgen_bench_data() -> List[Point]:
    """gets the computation data from a run generating T-SDDs 
    from the randomly generated benchmark problems"""
    points = []
    files_list: List[str] = []
    for path, _subdirs, files in os.walk("benchmarks/randgen/output_sdd"):
        for name in files:
            files_list.append(os.path.join(path, name))
    for filename in files_list:
        f = open(filename, encoding="utf8")
        data = json.load(f)
        if len(data) == 0 or data.get("timeout") is not None:
            points.append(Point(DataSource.THEORY_BDD, 0, 0, 0, filename.replace(
                'benchmarks/randgen/output_sdd/', ''), True))
            continue
        points.append(Point(DataSource.THEORY_BDD,
                            data["total computation time"],
                            data["All-SMT computation time"],
                            data["T-SDD"]["DD nodes"],
                            filename.replace('benchmarks/randgen/output_sdd/', ''), False))
    return points


def get_abstraction_bdd_from_randgen_bench_data() -> List[Point]:
    """gets the computation data from a run generating BDDs of 
    boolean abstractions from the randomly generated benchmark problems"""
    points = []
    files_list: List[str] = []
    for path, _subdirs, files in os.walk("benchmarks/randgen/output_abstraction"):
        for name in files:
            files_list.append(os.path.join(path, name))
    for filename in files_list:
        f = open(filename, encoding="utf8")
        data = json.load(f)
        if len(data) == 0 or data.get("timeout") is not None:
            points.append(Point(DataSource.ABSTRACTION_BDD, 0, 0, 0, filename.replace(
                'benchmarks/randgen/output_abstraction/', ''), True))
            continue
        points.append(Point(DataSource.ABSTRACTION_BDD,
                            data["total computation time"],
                            data["All-SMT computation time"],
                            data["T-BDD"]["DD nodes"],
                            filename.replace('benchmarks/randgen/output_abstraction/', ''), False))
    return points


def get_abstraction_sdd_from_randgen_bench_data() -> List[Point]:
    """gets the computation data from a run generating SDDs of 
    boolean abstractions from the randomly generated benchmark problems"""
    points = []
    files_list: List[str] = []
    for path, _subdirs, files in os.walk("benchmarks/randgen/output_abstraction_sdd"):
        for name in files:
            files_list.append(os.path.join(path, name))
    for filename in files_list:
        f = open(filename, encoding="utf8")
        data = json.load(f)
        if len(data) == 0 or data.get("timeout") is not None:
            points.append(Point(DataSource.ABSTRACTION_BDD, 0, 0, 0, filename.replace(
                'benchmarks/randgen/output_abstraction_sdd/', ''), True))
            continue
        points.append(Point(DataSource.ABSTRACTION_BDD,
                            data["total computation time"],
                            data["All-SMT computation time"],
                            data["T-SDD"]["DD nodes"],
                            filename.replace(
                                'benchmarks/randgen/output_abstraction_sdd/', ''),
                            False))
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
    max_theory = theory_points[0].allSMT_time
    max_abstraction = abstraction_points[0].allSMT_time

    for t_p in theory_points:
        if t_p.allSMT_time > max_theory:
            max_theory = t_p.allSMT_time
    for a_p in abstraction_points:
        if a_p.allSMT_time > max_abstraction:
            max_abstraction = a_p.allSMT_time

    edge = max(max_theory, max_abstraction) * 10

    for t_p in theory_points:
        if t_p.timeout:
            t_p.allSMT_time = edge
    for a_p in abstraction_points:
        if a_p.timeout:
            a_p.allSMT_time = edge

    for t_p in theory_points:
        for a_p in abstraction_points:
            if t_p.title == a_p.title:
                theory_list.append(t_p.allSMT_time)
                abstraction_list.append(a_p.allSMT_time)
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


def main() -> None:
    """main function"""
    pass
    # randgen BDD (DATA NOT READY)
    # t_points = get_theory_bdd_from_randgen_bench_data()
    # abstr_points = get_abstraction_bdd_from_randgen_bench_data()
    # randgen SDD (DATA NOT READY)
    # t_points = get_theory_sdd_from_randgen_bench_data()
    # abstr_points = get_abstraction_sdd_from_randgen_bench_data()
    # WMI BDD
    # t_points = get_theory_bdd_from_wmi_bench_data()
    # abstr_points = get_abstraction_bdd_from_wmi_bench_data()
    # WMI SDD
    # t_points = get_theory_sdd_from_wmi_bench_data()
    # abstr_points = get_abstraction_sdd_from_wmi_bench_data()
    # PARTIAL
    # a_points = get_randgen_bench_data('T-BDD','benchmarks/randgen/output')
    # # TOTAL
    # b_points = get_randgen_bench_data('T-BDD','benchmarks/randgen/output_total')
    # # PARTIAL PLF
    # c_points = get_randgen_bench_data('T-BDD','benchmarks/randgen/output_plf')
    # # TSETSIN
    # d_points = get_randgen_bench_data("T-BDD","benchmarks/randgen/output_tsetsin")

    # smtlib_tbdd = get_smtlib_QF_RDL_bench_data("T-BDD","benchmarks/smtlib/output_bdd")

    # smtlib_tsdd = get_smtlib_QF_RDL_bench_data("T-SDD","benchmarks/smtlib/output_sdd")

    # smt_points = get_allsmt_time_points(smtlib_tbdd,smtlib_tsdd)
    # size_points = get_nodes_points(smtlib_tbdd, smtlib_tsdd)
    # build_graphs(smt_points, size_points,"BDD","SDD")

    # smtlib_tbdd = get_smtlib_QF_RDL_bench_data("T-BDD","benchmarks/smtlib/output_bdd")

    # smtlib_ldd = get_smtlib_QF_RDL_bench_data("LDD","benchmarks/smtlib/output_ldd")

    # smt_points = get_time_points(smtlib_tbdd,smtlib_ldd)
    # size_points = get_nodes_points(smtlib_tbdd, smtlib_ldd)
    # build_graphs(smt_points, size_points,"BDD","LDD")

    # rgen_tbdd = get_smtlib_QF_RDL_bench_data("T-BDD","benchmarks/randgen/output")

    # rgen_tsdd = get_smtlib_QF_RDL_bench_data("T-SDD","benchmarks/randgen/output_sdd")

    # smt_points = get_allsmt_time_points(rgen_tbdd,rgen_tsdd)
    # size_points = get_nodes_points(rgen_tbdd, rgen_tsdd)
    # build_graphs(smt_points, size_points,"BDD","SDD")

    # smt_points = get_allsmt_time_points(a_points,c_points)
    # size_points = get_nodes_points(a_points, c_points)
    # build_graphs(smt_points, size_points,"NO PLF","PLF")

    # smt_points = get_allsmt_time_points(a_points,d_points)
    # size_points = get_nodes_points(a_points, d_points)
    # build_graphs(smt_points, size_points,"OLD PARTIAL","TSETSI PARTIAL")

    # --------------------------------------------------------------
    # LDD RANDGEN

    # ldd_randgen_ldds_points = get_ldd_randgen_bench_data(
    #     "LDD", "benchmarks/ldd_randgen/output_ldd")
    # ldd_randgen_bdds_points = get_ldd_randgen_bench_data(
    #     "T-BDD", "benchmarks/ldd_randgen/output")
    # ldd_randgen_abstraction_bdd_points = get_ldd_randgen_bench_data(
    #     "Abstraction BDD", "benchmarks/ldd_randgen/output_abstraction")

    # time_points = get_time_points(
    #     ldd_randgen_bdds_points, ldd_randgen_ldds_points)
    # size_points = get_nodes_points(
    #     ldd_randgen_bdds_points, ldd_randgen_ldds_points)
    # build_time_graph(time_points, "T-BDD", "LDD",
    #                  "plots/ldd_randgen/ldd_vs_tbdd_time.png")
    # build_size_graph(size_points, "T-BDD", "LDD",
    #                  "plots/ldd_randgen/ldd_vs_tbdd_size.png")

    # time_points = get_time_points(
    #     ldd_randgen_bdds_points, ldd_randgen_abstraction_bdd_points)
    # size_points = get_nodes_points(
    #     ldd_randgen_bdds_points, ldd_randgen_abstraction_bdd_points)
    # build_time_graph(time_points, "T-BDD", "Abs. BDD",
    #                  "plots/ldd_randgen/abstr_bdd_vs_tbdd_time.png")
    # build_size_graph(size_points, "T-BDD", "Abs. BDD",
    #                  "plots/ldd_randgen/abstr_bdd_vs_tbdd_size.png")

    # --------------------------------------------------------------
    # RANDGEN

    randgen_bdds_points = get_randgen_bench_data(
        "T-BDD", "benchmarks/randgen/output_tsetsin")
    randgen_abstraction_bdd_points = get_randgen_bench_data(
        "Abstraction BDD", "benchmarks/randgen/output_abstraction")
    randgen_sdds_points = get_randgen_bench_data(
        "T-SDD", "benchmarks/randgen/output_sdd")
    randgen_abstraction_sdd_points = get_randgen_bench_data(
        "Abstraction SDD", "benchmarks/randgen/output_abstraction_sdd")

    time_points = get_time_points(
        randgen_bdds_points, randgen_abstraction_bdd_points)
    size_points = get_nodes_points(
        randgen_bdds_points, randgen_abstraction_bdd_points)
    build_time_graph(time_points, "T-BDD", "Abs. BDD",
                     "plots/randgen/abstr_bdd_vs_tbdd_time.png")
    build_size_graph(size_points, "T-BDD", "Abs. BDD",
                     "plots/randgen/abstr_bdd_vs_tbdd_size.png")
    time_points = get_time_points(
        randgen_sdds_points, randgen_abstraction_sdd_points)
    size_points = get_nodes_points(
        randgen_sdds_points, randgen_abstraction_sdd_points)
    build_time_graph(time_points, "T-SDD", "Abs. SDD",
                     "plots/randgen/abstr_sdd_vs_tsdd_time.png")
    build_size_graph(size_points, "T-SDD", "Abs. SDD",
                     "plots/randgen/abstr_sdd_vs_tsdd_size.png")

    # --------------------------------------------------------------
    # SMTLIB QF RDL

    # qfrdl_ldds_points = get_smtlib_QF_RDL_bench_data(
    #     "LDD", "benchmarks/smtlib/output_ldd/non-incremental/QF_RDL")
    # qfrdl_bdds_points = get_smtlib_QF_RDL_bench_data(
    #     "T-BDD", "benchmarks/smtlib/output_bdd/non-incremental/QF_RDL")
    # qfrdl_abstraction_bdd_points = get_smtlib_QF_RDL_bench_data(
    #     "Abstraction BDD", "benchmarks/smtlib/output_abstraction_bdd/non-incremental/QF_RDL")
    # qfrdl_sdds_points = get_smtlib_QF_RDL_bench_data(
    #     "T-SDD", "benchmarks/smtlib/output_sdd/non-incremental/QF_RDL")
    # qfrdl_abstraction_sdd_points = get_smtlib_QF_RDL_bench_data(
    #     "Abstraction SDD", "benchmarks/smtlib/output_abstraction_sdd/non-incremental/QF_RDL")

    # time_points = get_time_points(
    #     qfrdl_bdds_points, qfrdl_ldds_points)
    # size_points = get_nodes_points(
    #     qfrdl_bdds_points, qfrdl_ldds_points)
    # build_time_graph(time_points, "T-BDD", "LDD",
    #                  "plots/smtlib/QF_RDL/ldd_vs_tbdd_time.png")
    # build_size_graph(size_points, "T-BDD", "LDD",
    #                  "plots/smtlib/QF_RDL/ldd_vs_tbdd_size.png")
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

    # qfuf_bdds_points = get_smtlib_QF_RDL_bench_data(
    #     "T-BDD", "benchmarks/smtlib/output_bdd/non-incremental/QF_UF")
    # qfuf_abstraction_bdd_points = get_smtlib_QF_RDL_bench_data(
    #     "Abstraction BDD", "benchmarks/smtlib/output_abstraction_bdd/non-incremental/QF_UF")
    # qfuf_sdds_points = get_smtlib_QF_RDL_bench_data(
    #     "T-SDD", "benchmarks/smtlib/output_sdd/non-incremental/QF_UF")
    # qfuf_abstraction_sdd_points = get_smtlib_QF_RDL_bench_data(
    #     "Abstraction SDD", "benchmarks/smtlib/output_abstraction_sdd/non-incremental/QF_UF")

    # time_points = get_time_points(
    #     qfuf_bdds_points, qfuf_abstraction_bdd_points)
    # size_points = get_nodes_points(
    #     qfuf_bdds_points, qfuf_abstraction_bdd_points)
    # build_time_graph(time_points, "T-BDD", "Abs. BDD",
    #                  "plots/smtlib/QF_UF/abstr_bdd_vs_tbdd_time.png")
    # build_size_graph(size_points, "T-BDD", "Abs. BDD",
    #                  "plots/smtlib/QF_UF/abstr_bdd_vs_tbdd_size.png")
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

    # qfuflra_ldds_points = get_smtlib_QF_RDL_bench_data(
    #     "LDD", "benchmarks/smtlib/output_ldd/non-incremental/QF_UFLRA")
    # qfuflra_bdds_points = get_smtlib_QF_RDL_bench_data(
    #     "T-BDD", "benchmarks/smtlib/output_bdd/non-incremental/QF_UFLRA")
    # qfuflra_abstraction_bdd_points = get_smtlib_QF_RDL_bench_data(
    #     "Abstraction BDD", "benchmarks/smtlib/output_abstraction_bdd/non-incremental/QF_UFLRA")
    # qfuflra_sdds_points = get_smtlib_QF_RDL_bench_data(
    #     "T-SDD", "benchmarks/smtlib/output_sdd/non-incremental/QF_RDL")
    # qfuflra_abstraction_sdd_points = get_smtlib_QF_RDL_bench_data(
    #     "Abstraction SDD", "benchmarks/smtlib/output_abstraction_sdd/non-incremental/QF_UFLRA")

    # time_points = get_time_points(
    #     qfuflra_bdds_points, qfuflra_ldds_points)
    # size_points = get_nodes_points(
    #     qfuflra_bdds_points, qfuflra_ldds_points)
    # build_time_graph(time_points, "T-BDD", "LDD",
    #                  "plots/smtlib/UFLRA/ldd_vs_tbdd_time.png")
    # build_size_graph(size_points, "T-BDD", "LDD",
    #                  "plots/smtlib/UFLRA/ldd_vs_tbdd_size.png")
    # time_points = get_time_points(
    #     qfuflra_bdds_points, qfuflra_abstraction_bdd_points)
    # size_points = get_nodes_points(
    #     qfuflra_bdds_points, qfuflra_abstraction_bdd_points)
    # build_time_graph(time_points, "T-BDD", "Abs. BDD",
    #                  "plots/smtlib/UFLRA/abstr_bdd_vs_tbdd_time.png")
    # build_size_graph(size_points, "T-BDD", "Abs. BDD",
    #                  "plots/smtlib/UFLRA/abstr_bdd_vs_tbdd_size.png")
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
