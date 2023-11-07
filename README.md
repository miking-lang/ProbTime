# ProbTime

ProbTime is a real-time probabilistic programming language (RTPPL). Using ProbTime, you can easily define probabilistic models that reason about timing aspects.

## Installing

Before installing the ProbTime compiler, `rtppl` (Real-Time Probabilistic Programming Language), you need to install [Miking](https://github.com/miking-lang/miking/) and [Miking DPPL](https://github.com/miking-lang/miking-dppl). In addition, you need to configure the `MCORE_LIBS` variable such that it includes the paths to the Miking and Miking DPPL standard libraries:
```
MCORE_LIBS="stdlib=/path/to/Miking/stdlib:coreppl=/path/to/coreppl/stdlib"
```

Following the above installations, you can install the ProbTime compiler by running `make install` at the root of this repository. This installs the ProbTime compiler `rtppl` and the configuration binary `rtppl-configure` (ensure that `$(HOME)/.local/bin` is in your path). Run `make uninstall` to undo the installation.

## Overview

A ProbTime program defines a system of tasks which can interact with each other. The ProbTime compiler produces an executable for each task defined in the ProbTime program. Tasks communicate with each other via ports using messages (timestamped values). When a task writes data to an output port, it is sent to all connected input ports (≥ 1). When a task reads from an input port, which may only receive data from one output port, it receives a sequence of newly arrived messages. Tasks can also communicate with external code using sensors (treated as an output port) and actuators (treated as an input port). A sensor provides input from an external source to one or more ProbTime tasks. An actuator propagates output from a ProbTime task to an external destination.

### Program structure

A ProbTime program consists of a series of top-level definitions followed by a system specification. We support three kinds of top-level definitions:
* Task templates (`template`) which we use in the system specification to instantiate tasks. The templates can take arguments, allowing us to reuse them for instantiating multiple similar tasks (e.g., sensors on different positions on a car). Inside templates, we can specify delays (`delay`) and perform inference on probabilistic models (`infer`).
* Probabilistic models (`model`) from which we can infer distributions. We can only use `sample`, `observe`, and `resample` inside a probabilistic model.
* Function definitions (`def`) in which we can perform arbitrary computations. These functions can be used by templates and probabilistic models.

### Examples

For concrete examples of ProbTime programs, we refer to the `examples` directory.

### Configuration

Prior to running the configuration, we need to compile the ProbTime program by passing it to the `rtppl` command. Next, we need to specify a task-to-core mapping for each task. We do this by listing the tasks and the core index they are mapped to (we assume tasks run exclusively on a single core) in a file `task-core-map.txt`. The concrete examples show how to do this.

Each task may perform inference using probabilistic models. However, you don't have to specify how to perform inference. We perform Sequential Monte Carlo (SMC) under the hood. We provide the `rtppl-configure` binary to determine how many particles to use in each inference. It takes a runner command, with which to run all tasks (providing pre-recorded data), and repeatedly runs the tasks to find a fair allocation of execution times or number of particles (if `--particle-fairness` is specified), based on how important tasks are and based on the worst-case execution times (WCETs) it finds.

After the configuration, each task `t` will have a configuration file `t.config` specifying the number of particles to use, the maximum CPU execution time to use (used to detect and report overruns), and the slowdown factor (used for simulation purposes). You can manually create the configuration files to avoid having to run the configuration.

### Limitations

Currently, we assume each task consists of an initialization (any number of finite statements) followed by an infinite loop (`while true { ... }`). Due to how our configuration works, we further assume that:
1. The infinite loop contains exactly one use of `delay` with a fixed argument (i.e., we assume tasks are periodic).
2. The infinite loop contains at most one use of `infer`. This inference is the one for which we control the number of particles. All uses of `infer` in the initialization use a fixed number of particles (currently, 100).

ProbTime currently only works on Linux. We assume tasks run exclusively on a single core (e.g., by using `taskset`), which is currently not supported on MacOS.

## External behavior

In this part, we provide necessary information for defining an underlying platform for relaying messages between ProbTime tasks as well as external code interacting with ProbTime tasks via sensors and actuators.

All connections between tasks are listed in the `connections` list of the `network.json` file containing a JSON encoding of the system specification. For each input port of a task, the compiler creates a shared memory object (`shm_open`) with memory mapping (`mmap`) using a buffer size of `2^22` (hard-coded for now). Assume we have a task `A` with an input port `in`. If the connected output port belongs to another task, then it will write directly to a shared memory object called `A-in`. Otherwise, if the output port is a sensor, the underlying platform is responsible for writing to it using a correct format.

The binary format of each message starts with a 64-bit size (for the timestamp and the payload). We use this as distributions may vary in size. Next, we encode the 64-bit timestamp (an absolute value). Finally, the remaining part of the message consists of the payload (of length `size - 8` bytes). Currently, the compiler only has support for a few specific kinds of data. For a comprehensive example using this in practice via a Python implementation, see [this repo](https://github.com/larshum/rtppl-experiments).

### Numerical Values

We support sending integer (`Int`) and floating-point (`Float`) numerical values, both represented using 64-bits of data.

### Records

We support records of integers and distributions of records of floats. Each element of a record is encoded as described above. We store the values in shortlex order (ordered by length and alphabetically among strings of the same length) of the record labels. For example, a record `{aa: Int, x : Int, y : Int}` would be encoded such that the value of `x` comes first, followed by `y`, and ending with `aa`.

### Distributions

We support encoding empirical distrbutions over records of floating-point values. An empirical distribution consists of a finite number of particles, each consisting of a weight and data (either a record of floats or a float). We encode each particle in sequence, starting with its 64-bit floating-point weight followed by its data. Based on the message size and knowledge of what type of data is being sent, we can compute the number of particles from the message size.
