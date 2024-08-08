# Coin

This is a simple ProbTime program making use of a probabilistic model to iteratively estimate the bias of a coin given observed outcomes from flipping the coin.

## Running

This example requires Python. Run `make`, and it will compile the `coin.rpl` example. The Python producer script provides the outcomes of artificial coin flips, and the consumer script prints the expected bias and the standard deviation as provided by the ProbTime task. To remove the extra files produced as part of the compilation, run `make clean`.

The ProbTime task prints the timestamp and value of the observations it receives (0.0 = heads, 1.0 = tails). When we run the program using the biased producer, the consumer prints the expected value and standard deviation based on current observations. We can make two observations from this:
 1. The expected bias converges toward 0.3 as the program runs.
 2. The standard deviation decreases as we make more observations.
