# ProbTime

ProbTime is a real-time probabilistic programming language. Using ProbTime, you can easily define probabilistic models that reason about timing aspects.

## Installing

Before installing the ProbTime compiler, `rtppl` (Real-Time Probabilistic Programming Language), you need to install Miking and Miking DPPL. In addition, you need to configure the `MCORE_LIBS` variable such that it includes the paths to the Miking and Miking DPPL standard libraries:
```
MCORE_LIBS="stdlib=/path/to/Miking/stdlib:coreppl=/path/to/coreppl/stdlib"
```

You can then install the ProbTime compiler by running `make install` at the root of this repository. This results in

* The ProbTime compiler binary `rtppl` being placed at `$(HOME)/.local/bin`
* The source files under `src/` being placed at `$(HOME)/.local/src/rtppl/`
* The RTPPL support library being installed as an OPAM library (in the current switch)

Run `make uninstall` to undo the above changes.

## Overview

A ProbTime program defines a system of tasks which can interact with each other as well as external code. The compiler produces an executable for each task defined in the program, which can be distributed arbitrarily across different nodes. We assume the existence of an underlying system which handles the data transfer between task executables. Because of this assumption, the executables are platform agnostic - we can run a task on different nodes without having to recompile the ProbTime program.

Using sensors and actuators, a ProbTime program can interact with external code. A sensor provides input from an external source to one or more ProbTime tasks, while an actuator propagates output from a ProbTime task to an external destination. The messages passed through these consist of a timestamp and a payload.

### Program structure

A ProbTime program consists of a series of top-level definitions followed by a network system specification. In the top-level definitions, we define task templates from which we later define the tasks, as well as probabilistic models and regular functions that the templates can make use of. The system specification consists of three parts, which must be defined in the stated order:

1. External sensor inputs and actuator outputs, giving them a name as well as a type of their payload.
2. Task definitions in terms of previously defined task templates.
3. Declaration of how tasks, sensors, and actuators are connected with each other.

### Examples

For concrete examples of how to write and use ProbTime programs, we refer to the `examples/` directory.

## External behavior

In this part, we provide necessary information for defining an underlying platform for relaying messages between ProbTime tasks as well as external code interacting with ProbTime tasks via sensors and actuators.

For each task defined in the ProbTime program, our compiler produces one executable named after the task. In addition, for each input and output port of the task, the compiler will produce a file. For example, if we compile a program defining task `abc` with input port `in1` and output port `out1` the compiler will emit an executable `abc` and two files `abc-in1` and `abc-out1`. The compiler also generates a system specification file in a JSON format, called `network.json`. This file declares the names of the `tasks` defined in the program, as well as the `sensors` and `actuators`. In addition, it defines the `connections` based on the system specification. For example, if we declare the input from a sensor `x` to be passed to the input port `in1` of task `abc`, the `connections` list contains an entry `{"from": "x", "to": "abc-in1"}`.

The binary format of a message is as follows. The first 64 bits encode the size of the remaining part of the message. We use this as certain kinds of data (distributions) may vary in size. The following 64 bits encode the timestamp associated with the message and the remaining part consists of the payload (containing `size - 8` bytes of data). Currently, the compiler supports two kinds of data.

### Floats

A floating-point number (`Float`) is encoded as a 64-bit number.

### Distributions

We support encoding empirical distributions over floating-point numbers or records of floating-point numbers, e.g., `Dist(Float)` or `Dist(Pos)` where `Pos` is an alias for a record `{x : Float, y : Float}`.

An empirical distribution consists of a finite number of particles, each of which has a weight and a value. We encode the particles of the distribution one by one. Each particle starts with a 64-bit floating-point number encoding its weight. If the data of the particles are floats, we simply encode them as 64-bit numbers. Otherwise, if the data is a record type consisting only of floating-point numbers, these are laid out as 64-bit floating-point numbers in memory based on the shortlex order of the labels (sorted first by length and then lexicographically among those with the same length).
