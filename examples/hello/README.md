# Hello

This is a hello world example of ProbTime, showing many of the important real-time programming features of the language.

In this example, we have two tasks `a` and `b` as well as a sensor input `src` and actuator output `dst`. These are connected as a pipeline, with the input from `src` being passed through `a` and `b` before the output reaches the `dst` actuator.

## Running

This example requires Python. Run `make`, and it will compile the `hello.rpl` example. The Python scripts are used as the platform, which produces the sensor data, relays data between `a` and `b`, as well as consumes the actuator data. To remove the extra files produced as part of the compilation, run `make clean`.

Note that the tasks `a` and `b` could run on different computers without modifying the ProbTime code. This would, however, require that the Python scripts send and receive data via sockets rather than relaying the data directly through the files.
