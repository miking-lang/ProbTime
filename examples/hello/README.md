# Hello

This is a hello world example of ProbTime, showing many of the important real-time programming features of the language.

In this example, we have two tasks `a` and `b` as well as a sensor input `src` (from `producer.py`) and actuator output `dst` (received by `consumer.py`). These are connected as a pipeline, with the data from the producer being received by `a` and sent to `b` before reaching the consumer.

## Running

This example requires Python. Run `make`, and it will compile the `hello.rpl` example. The Python scripts are used as the platform, which produces the sensor data, relays data between `a` and `b`, as well as consumes the actuator data. To remove the extra files produced as part of the compilation, run `make clean`.
