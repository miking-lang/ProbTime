# ProbTime

ProbTime is a real-time probabilistic programming language (RTPPL). Using ProbTime, you can easily define probabilistic models that reason about timing aspects. ProbTime is supported on Linux only.

## Installing

The ProbTime compiler `rtppl` (for Real-Time Probabilistic Programming Language) depends on Miking and Miking DPPL, both of which are included as submodules (`miking` and `miking-dppl` respectively). These refer to commits of those repositories for which ProbTime has been verified to work correctly. Run
```
git submodule init
git submodule update
```
to initialize the submodules, and then follow the installation instructions in the respctive repository to install Miking and Miking DPPL. After installing them, you need to configure the `MCORE_LIBS` variable such that it includes paths to the Miking and Miking DPPL standard libraries. For instance, this could look like
```
export MCORE_LIBS="stdlib=/path/to/Miking/stdlib:coreppl=/path/to/coreppl/stdlib"
```
After setting the `MCORE_LIBS` variable, you can install the ProbTime compiler by running
```
make install
```
This installs the ProbTime compiler `rtppl` and the automated configuration binary `rtppl-configure` in `$(HOME)/.local/bin` (ensure this is included in your path). Run `make uninstall` to undo the installation.

## Overview

A ProbTime program defines a system of tasks which can interact with each other. The ProbTime compiler produces an executable for each task defined in the ProbTime program. Tasks communicate with each other via ports using messages (timestamped values). When a task writes data to an output port, it is sent to all connected input ports (≥ 1) at the end of the task instance. When a task reads from an input port, which may only receive data from one output port, it retrieves a sequence of messages. Tasks can also communicate with external code using sensors (treated as an output port) and actuators (treated as an input port). A sensor provides input from an external source to one or more ProbTime tasks. An actuator propagates output from a ProbTime task to an external destination.

### Program structure

A ProbTime program consists of a series of top-level definitions followed by a system specification. We support three kinds of top-level definitions:
* Task templates (`template`) which we use in the system specification to instantiate tasks. The templates can take arguments, allowing us to reuse them for instantiating multiple similar tasks (e.g., sensors on different positions on a car). Inside templates, we can specify delays (`delay`) and perform inference on probabilistic models (`infer`).
* Probabilistic models (`model`) from which we can infer distributions. We can only use `sample`, `observe`, and `resample` inside a probabilistic model.
* Function definitions (`def`) in which we can perform arbitrary computations. These functions can be used by templates and probabilistic models.

### Examples

For concrete examples of ProbTime programs, we refer to the `examples` directory.

### Configuration

Before running configuration, we need to compile the ProbTime program by passing its name to the `rtppl` command. The compilation produces a binary for each task defined in the ProbTime program and a system specification JSON file `system.json`. Before running the configuration, we need to specify the task-to-core mapping by setting the `core` property of each task to the desired index (by default, they are all mapped to core #0). Here, we can also specify the relative importance of each task via the `importance`, which impacts how resources (execution time or particle count) are distributed among the tasks. The importance should be set to `0.0` for tasks that contain no configurable inference.

Each task may perform probabilistic inference, either by specifying a fixed number of particles to run or by omitting it. The configuration automatically finds the maximum number of particles to use in the latter case for all tasks, in a fair way. We provide the `rtppl-configure` binary to determine how many particles to use in each use of `infer` (the keyword associated with probabilistic inference). It takes a runner command, using which it can run all tasks of the ProbTime system (providing pre-recorded data), and repeatedly runs the tasks to find a fair allocation of execution times or particle counts (depending on whether `--execution-time-fairness` or `--particle-fairness` is used), based on the importance of each task and on the measured worst-case execution times (WCETs).

While the automatic configuration is running, it will print the particle count assigned to each task and the measured WCETs. After the configuration has finished, it will update the `system.json` file by setting the `particles` property (determining the particle count of configurable infers) based on its findings. Users can employ custom tools for determining the particle count or manually fill in the desired values to avoid having to run the configuration.

### Limitations

Currently, our automatic configuration assumes all tasks in the system are periodic. If any task is sporadic, you have two options:
1. Manually set the particle count of all `infer`s in the system.
2. Perform your own automatic configuration, by setting the particle count in the `system.json` file.

## External behavior

In this part, we provide necessary information for defining an underlying platform for relaying messages between ProbTime tasks as well as external code interacting with ProbTime tasks via sensors and actuators.

All connections between tasks are listed in the `connections` list of the `system.json` file containing a JSON encoding of the system specification. For each input port of a task, the compiler creates a shared memory object (`shm_open`) with memory mapping (`mmap`) using a buffer size of `2^22` (hard-coded for now). Assume we have a task `A` with an input port `in`. If the connected output port belongs to another task, then it will write directly to a shared memory object called `A-in`. Otherwise, if the output port is a sensor, the underlying platform is responsible for writing to it using a correct format.

The binary format of each message starts with a 64-bit size (for the timestamp and the payload). We use this as distributions may vary in size. Next, we encode the 64-bit timestamp (an absolute value). Finally, the remaining part of the message consists of the payload (of length `size - 8` bytes). Currently, the compiler only has support for a few specific kinds of data. For a comprehensive example using this in practice via a Python implementation, see [this repo](https://github.com/larshum/rtppl-experiments).

### Numerical Values

We support sending integer (`Int`) and floating-point (`Float`) numerical values, both represented using 64-bits of data.

### Records

We support records of integers and distributions of records of floats. Each element of a record is encoded as described above. We store the values in shortlex order (ordered by length and alphabetically among strings of the same length) of the record labels. For example, a record `{aa: Int, x : Int, y : Int}` would be encoded such that the value of `x` comes first, followed by `y`, and ending with `aa`.

### Distributions

We support encoding empirical distrbutions over records of floating-point values. An empirical distribution consists of a finite number of particles, each consisting of a weight and data (either a record of floats or a float). We encode each particle in sequence, starting with its 64-bit floating-point weight followed by its data. Based on the message size and knowledge of what type of data is being sent, we can compute the number of particles from the message size.
