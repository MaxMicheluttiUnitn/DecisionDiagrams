"""main and functions to plot the results of the program running on benchmarks"""
from enum import Enum
import json
import os
from dataclasses import dataclass
#from pprint import pprint
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
            points.append(Point(DataSource.ABSTRACTION_BDD,0,0,"mutex/"+filename,True))
            continue
        if data["all sat result"] == "UNSAT":
            points.append(Point(DataSource.ABSTRACTION_BDD,
                          data["total computation time"], 1,
                          "mutex/"+filename,False))
        else:
            points.append(Point(DataSource.ABSTRACTION_BDD,
                          data["total computation time"],
                          data["SDD"]["DD nodes"], "mutex/"+filename, False))

    # retrieving xor result
    files = os.listdir("benchmarks/wmi/output_abstraction_sdd/xor")
    files.sort()
    for filename in files:
        f = open("benchmarks/wmi/output_abstraction_sdd/xor/" +
                 filename, encoding="utf8")
        data = json.load(f)
        if len(data) == 0 or data.get("timeout") is not None:
            points.append(Point(DataSource.ABSTRACTION_BDD,0,0,"xor/"+filename,True))
            continue
        if data["all sat result"] == "UNSAT":
            points.append(Point(DataSource.ABSTRACTION_BDD,
                          data["total computation time"], 1, "xor/"+filename,False))
        else:
            points.append(Point(DataSource.ABSTRACTION_BDD,
                          data["total computation time"], data["SDD"]["DD nodes"], "xor/"+filename,False))

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
            points.append(Point(DataSource.ABSTRACTION_BDD,0,0,"mutex/"+filename,True))
            continue
        if data["all sat result"] == "UNSAT":
            points.append(Point(DataSource.ABSTRACTION_BDD,
                          data["total computation time"], 1,
                          "mutex/"+filename,False))
        else:
            points.append(Point(DataSource.ABSTRACTION_BDD,
                          data["total computation time"],
                          data["BDD"]["DD nodes"], "mutex/"+filename, False))

    # retrieving xor result
    files = os.listdir("benchmarks/wmi/output_abstraction/xor")
    files.sort()
    for filename in files:
        f = open("benchmarks/wmi/output_abstraction/xor/" +
                 filename, encoding="utf8")
        data = json.load(f)
        if len(data) == 0 or data.get("timeout") is not None:
            points.append(Point(DataSource.ABSTRACTION_BDD,0,0,"xor/"+filename,True))
            continue
        if data["all sat result"] == "UNSAT":
            points.append(Point(DataSource.ABSTRACTION_BDD,
                          data["total computation time"], 1, "xor/"+filename,False))
        else:
            points.append(Point(DataSource.ABSTRACTION_BDD,
                          data["total computation time"], data["BDD"]["DD nodes"], "xor/"+filename,False))

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
            points.append(Point(DataSource.THEORY_SDD,0,0,"mutex/"+filename,True))
            continue
        if data["all sat result"] == "UNSAT":
            points.append(Point(DataSource.THEORY_SDD,
                          data["total computation time"], 1, "mutex/"+filename,False))
        else:
            points.append(Point(DataSource.THEORY_SDD,
                          data["total computation time"],
                          data["SDD"]["DD nodes"], "mutex/"+filename,False))

    # retrieving xor result
    files = os.listdir("benchmarks/wmi/output_sdd/xor")
    for filename in files:
        f = open("benchmarks/wmi/output_sdd/xor/"+filename, encoding="utf8")
        data = json.load(f)
        if len(data) == 0 or data.get("timeout") is not None:
            points.append(Point(DataSource.THEORY_SDD,0,0,"xor/"+filename,True))
            continue
        if data["all sat result"] == "UNSAT":
            points.append(Point(DataSource.THEORY_SDD,
                          data["total computation time"], 1, "xor/"+filename,False))
        else:
            points.append(Point(DataSource.THEORY_SDD,
                          data["total computation time"], data["SDD"]["DD nodes"], "xor/"+filename,False))

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
            points.append(Point(DataSource.THEORY_BDD,0,0,"mutex/"+filename,True))
            continue
        if data["all sat result"] == "UNSAT":
            points.append(Point(DataSource.THEORY_BDD,
                          data["total computation time"], 1, "mutex/"+filename,False))
        else:
            points.append(Point(DataSource.THEORY_BDD,
                          data["total computation time"],
                          data["BDD"]["DD nodes"], "mutex/"+filename,False))

    # retrieving xor result
    files = os.listdir("benchmarks/wmi/output/xor")
    for filename in files:
        f = open("benchmarks/wmi/output/xor/"+filename, encoding="utf8")
        data = json.load(f)
        if len(data) == 0 or data.get("timeout") is not None:
            points.append(Point(DataSource.THEORY_BDD,0,0,"xor/"+filename,True))
            continue
        if data["all sat result"] == "UNSAT":
            points.append(Point(DataSource.THEORY_BDD,
                          data["total computation time"], 1, "xor/"+filename,False))
        else:
            points.append(Point(DataSource.THEORY_BDD,
                          data["total computation time"], data["BDD"]["DD nodes"], "xor/"+filename,False))

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
            points.append(Point(DataSource.THEORY_BDD,0,0,filename.replace('benchmarks/randgen/output/', ''),True))
            continue
        if data["all sat result"] == "UNSAT":
            points.append(Point(DataSource.THEORY_BDD,
                          data["total computation time"], 1,
                          filename.replace('benchmarks/randgen/output/', ''),False))
        else:
            points.append(Point(DataSource.THEORY_BDD,
                          data["total computation time"],
                          data["BDD"]["DD nodes"],
                          filename.replace('benchmarks/randgen/output/', ''),False))
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
            points.append(Point(DataSource.THEORY_BDD,0,0,filename.replace('benchmarks/randgen/output_sdd/', ''),True))
            continue
        if data["all sat result"] == "UNSAT":
            points.append(Point(DataSource.THEORY_BDD,
                          data["total computation time"], 1,
                          filename.replace('benchmarks/randgen/output/', ''),False))
        else:
            points.append(Point(DataSource.THEORY_BDD,
                          data["total computation time"],
                          data["SDD"]["DD nodes"],
                          filename.replace('benchmarks/randgen/output/', ''),False))
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
            points.append(Point(DataSource.ABSTRACTION_BDD,0,0,filename.replace('benchmarks/randgen/output_abstraction/', ''),True))
            continue
        if data["all sat result"] == "UNSAT":
            points.append(Point(DataSource.ABSTRACTION_BDD,
                          data["total computation time"],
                          1,
                          filename.replace('benchmarks/randgen/output_abstraction/', ''),False))
        else:
            points.append(Point(DataSource.ABSTRACTION_BDD,
                          data["total computation time"],
                          data["BDD"]["DD nodes"],
                          filename.replace('benchmarks/randgen/output_abstraction/', ''),False))
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
            points.append(Point(DataSource.ABSTRACTION_BDD,0,0,filename.replace('benchmarks/randgen/output_abstraction_sdd/', ''),True))
            continue
        if data["all sat result"] == "UNSAT":
            points.append(Point(DataSource.ABSTRACTION_BDD,
                          data["total computation time"],
                          1,
                          filename.replace('benchmarks/randgen/output_abstraction_sdd/', ''),False))
        else:
            points.append(Point(DataSource.ABSTRACTION_BDD,
                          data["total computation time"],
                          data["SDD"]["DD nodes"],
                          filename.replace('benchmarks/randgen/output_abstraction_sdd/', ''),False))
    return points


def get_time_points(
        theory_points: List[Point],
        abstraction_points: List[Point]) -> Tuple[List[float], List[float],int]:
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

    edge = max(max_theory,max_abstraction) * 10
    
    for t_p in theory_points:
        if t_p.timeout:
            t_p.computation_time = edge
    for a_p in abstraction_points:
        if a_p.timeout:
            a_p.computation_time=edge
    
    for t_p in theory_points:
        for a_p in abstraction_points:
            if t_p.title == a_p.title:
                theory_list.append(t_p.computation_time)
                abstraction_list.append(a_p.computation_time)
                break
    return (theory_list, abstraction_list, edge)


def get_nodes_points(
        theory_points: List[Point],
        abstraction_points: List[Point]) -> Tuple[List[float], List[float],int]:
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

    edge = max(max_theory,max_abstraction) *10
    
    for t_p in theory_points:
        if t_p.timeout:
            t_p.dd_nodes = edge
    for a_p in abstraction_points:
        if a_p.timeout:
            a_p.dd_nodes=edge

    for t_p in theory_points:
        for a_p in abstraction_points:
            if t_p.title == a_p.title:
                theory_list.append(t_p.dd_nodes)
                abstraction_list.append(a_p.dd_nodes)
                break
    return (theory_list, abstraction_list, edge)


def main() -> None:
    """main function"""
    # randgen BDD (DATA NOT READY)
    # t_points = get_theory_bdd_from_randgen_bench_data()
    # abstr_points = get_abstraction_bdd_from_randgen_bench_data()
    # randgen SDD (DATA NOT READY)
    # t_points = get_theory_sdd_from_randgen_bench_data()
    # abstr_points = get_abstraction_sdd_from_randgen_bench_data()
    # WMI BDD
    #t_points = get_theory_bdd_from_wmi_bench_data()
    #abstr_points = get_abstraction_bdd_from_wmi_bench_data()
    # WMI SDD
    t_points = get_theory_sdd_from_wmi_bench_data()
    abstr_points = get_abstraction_sdd_from_wmi_bench_data()

    time_points = get_time_points(t_points, abstr_points)
    size_points = get_nodes_points(t_points, abstr_points)

    plt.scatter(time_points[0], time_points[1], marker='s')
    plt.xlabel("T-DD")
    plt.ylabel("Abstr. DD")
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
    plt.axvline(x = time_points[2],ls="--", c=".3")
    plt.axhline(y = time_points[2],ls="--", c=".3")
    plt.axis('square')
    plt.show()

    plt.scatter(size_points[0], size_points[1], marker='s')
    plt.xlabel("T-DD")
    plt.ylabel("Abstr. DD")
    plt.title("DD size in nodes")
    ax = plt.gca()
    ax.set_yscale('log')
    ax.set_xscale('log')
    ax.set_aspect('equal', adjustable='box')
    diag_line, = ax.plot(ax.get_xlim(), ax.get_ylim(), ls="--", c=".3")
    plt.axvline(x = size_points[2],ls="--", c=".3")
    plt.axhline(y = size_points[2],ls="--", c=".3")
    def on_change(_axes):
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
