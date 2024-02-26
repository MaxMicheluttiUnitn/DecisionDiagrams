"""main and functions to plot the results of the program running on benchmarks"""
from enum import Enum
import json
import os
from dataclasses import dataclass
from typing import List, Tuple
import matplotlib.pyplot as plt


class DataSource(Enum):
    """annotation to keep track of which computation was used"""
    THEORY_BDD = 1
    ABSTRACTION_BDD = 2
    THEORY_SDD = 3
    ABSTRACTION_SDD = 4


@dataclass
class Point:
    """a Point that can be plotted"""
    source: DataSource
    computation_time: float
    dd_nodes: int
    title: str


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
        if len(data) == 0:
            print("Timeout")
            continue
        if data["all sat result"] == "UNSAT":
            points.append(Point(DataSource.ABSTRACTION_BDD,
                          data["total computation time"], 1,
                          "mutex/"+filename))
        else:
            points.append(Point(DataSource.ABSTRACTION_BDD,
                          data["total computation time"],
                          data["BDD"]["DD nodes"], "mutex/"+filename))

    # retrieving xor result
    files = os.listdir("benchmarks/wmi/output_abstraction/xor")
    files.sort()
    for filename in files:
        f = open("benchmarks/wmi/output_abstraction/xor/" +
                 filename, encoding="utf8")
        data = json.load(f)
        if len(data) == 0:
            print("Timeout")
            continue
        if data["all sat result"] == "UNSAT":
            points.append(Point(DataSource.ABSTRACTION_BDD,
                          data["total computation time"], 1, "xor/"+filename))
        else:
            points.append(Point(DataSource.ABSTRACTION_BDD,
                          data["total computation time"], data["BDD"]["DD nodes"], "xor/"+filename))

    return points


def get_theory_bdd_from_wmi_bench_data() -> List[Point]:
    """gets the computation data from a run generating T-BDDs from the WMI benchmark problems"""
    points = []

    # retrieving mutex result
    files = os.listdir("benchmarks/wmi/output/mutex")
    for filename in files:
        f = open("benchmarks/wmi/output/mutex/"+filename, encoding="utf8")
        data = json.load(f)
        if len(data) == 0:
            continue
        if data["all sat result"] == "UNSAT":
            points.append(Point(DataSource.THEORY_BDD,
                          data["total computation time"], 1, "mutex/"+filename))
        else:
            points.append(Point(DataSource.THEORY_BDD,
                          data["total computation time"],
                          data["BDD"]["DD nodes"], "mutex/"+filename))

    # retrieving xor result
    files = os.listdir("benchmarks/wmi/output/xor")
    for filename in files:
        f = open("benchmarks/wmi/output/xor/"+filename, encoding="utf8")
        data = json.load(f)
        if len(data) == 0:
            continue
        if data["all sat result"] == "UNSAT":
            points.append(Point(DataSource.THEORY_BDD,
                          data["total computation time"], 1, "xor/"+filename))
        else:
            points.append(Point(DataSource.THEORY_BDD,
                          data["total computation time"], data["BDD"]["DD nodes"], "xor/"+filename))

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
        if len(data) == 0:
            print("Timeout")
            continue
        if data["all sat result"] == "UNSAT":
            points.append(Point(DataSource.THEORY_BDD,
                          data["total computation time"], 1,
                          filename.replace('benchmarks/randgen/output/', '')))
        else:
            points.append(Point(DataSource.THEORY_BDD,
                          data["total computation time"],
                          data["BDD"]["DD nodes"],
                          filename.replace('benchmarks/randgen/output/', '')))
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
        if len(data) == 0:
            print("Timeout")
            continue
        if data["all sat result"] == "UNSAT":
            points.append(Point(DataSource.THEORY_BDD,
                          data["total computation time"],
                          1,
                          filename.replace('benchmarks/randgen/output_abstraction/', '')))
        else:
            points.append(Point(DataSource.THEORY_BDD,
                          data["total computation time"],
                          data["BDD"]["DD nodes"],
                          filename.replace('benchmarks/randgen/output_abstraction/', '')))
    return points


def get_time_points(
        theory_points: List[Point],
        abstraction_points: List[Point]) -> Tuple[List[float], List[float]]:
    """translate data into plottable points comparing time"""
    theory_list = []
    abstraction_list = []
    for t_p in theory_points:
        for a_p in abstraction_points:
            if t_p.title == a_p.title:
                theory_list.append(t_p.computation_time)
                abstraction_list.append(a_p.computation_time)
                break
    return (theory_list, abstraction_list)


def get_nodes_points(
        theory_points: List[Point],
        abstraction_points: List[Point]) -> Tuple[List[float], List[float]]:
    """translate data into plottable points comparing DD size in nodes"""
    theory_list = []
    abstraction_list = []
    for t_p in theory_points:
        for a_p in abstraction_points:
            if t_p.title == a_p.title:
                theory_list.append(t_p.dd_nodes)
                abstraction_list.append(a_p.dd_nodes)
                break
    return (theory_list, abstraction_list)


def main() -> None:
    """main function"""
    t_points = get_theory_bdd_from_randgen_bench_data()
    abstr_points = get_abstraction_bdd_from_randgen_bench_data()
    #t_points = get_theory_bdd_from_wmi_bench_data()
    #abstr_points = get_abstraction_bdd_from_wmi_bench_data()
    time_points = get_time_points(t_points, abstr_points)
    size_points = get_nodes_points(t_points, abstr_points)

    plt.scatter(time_points[0], time_points[1])
    plt.xlabel("T-BDD")
    plt.ylabel("Abstr. BDD")
    plt.title("Computation Time")
    ax = plt.gca()
    ax.set_yscale('log')
    ax.set_xscale('log')
    ax.set_aspect('equal', adjustable='box')
    diag_line, = ax.plot(ax.get_xlim(), ax.get_ylim(), ls="--", c=".3")
    def on_change_time(axes):
        x_lims = ax.get_xlim()
        y_lims = ax.get_ylim()
        diag_line.set_data(x_lims, y_lims)
    ax.callbacks.connect('xlim_changed', on_change_time)
    ax.callbacks.connect('ylim_changed', on_change_time)
    plt.axis('square')
    plt.show()

    plt.scatter(size_points[0], size_points[1])
    plt.xlabel("T-BDD")
    plt.ylabel("Abstr. BDD")
    plt.title("DD size in nodes")
    ax = plt.gca()
    ax.set_aspect('equal', adjustable='box')
    diag_line, = ax.plot(ax.get_xlim(), ax.get_ylim(), ls="--", c=".3")
    def on_change(axes):
        x_lims = ax.get_xlim()
        y_lims = ax.get_ylim()
        diag_line.set_data(x_lims, y_lims)
    ax.callbacks.connect('xlim_changed', on_change)
    ax.callbacks.connect('ylim_changed', on_change)
    plt.axis('square')
    plt.show()


def test_plotting_lib() -> None:
    """test plotting lib"""
    x = [5, 7, 8, 7, 2, 17, 2, 9, 4, 11, 12, 9, 6]
    y = [99, 86, 87, 88, 111, 86, 103, 87, 94, 78, 77, 85, 86]
    plt.scatter(x, y)
    plt.show()


if __name__ == "__main__":
    main()
