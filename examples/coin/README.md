# Coin

This is a simple ProbTime program making use of a probabilistic model to iteratively estimate the bias of a coin given observed outcomes from flipping the coin.

## Running

This example requires Python. Run `make`, and it will compile the `coin.rpl` example. The Python scripts produce artificial coin flip outcomes and print the expected bias of the distribution of the ProbTime task. To remove the extra files produced as part of the compilation, run `make clean`.

The ProbTime task prints out the timestamp and value of the observations it receives. The consumer script prints the expected bias produced by the ProbTime task after it is written. When we run the program, using the biased producer (probability of 0.7 to produce a heads, encoded as 0.0) we see that the expected bias converges toward 0.3 as the program runs.
